#!/usr/bin/env python3
"""국토교통부 아파트 매매·전월세 실거래 수집기 (GitHub Actions에서 실행).

결과물
  out/summary.md  사람이(그리고 모니터링 작업이) 바로 읽는 요약
  out/volume.json 권역·감시지역별 계약월 거래 건수
  out/deals.json  조건에 맞는 실거래 전체
  out/run.json    실행 정보(호출 수, 오류, 응답 필드 확인용 샘플)
  state/peaks.json 단지·평형별 역대 최고가(중개·유형미확인 거래 기준)
  state/codes.json 행정구역 개편으로 새로 생긴 시군구 코드 탐색 결과

환경변수
  DATA_GO_KR_KEY  공공데이터포털 일반 인증키(Decoding)
  BACKFILL_FROM   (선택) 신고가 이력을 이 달부터 채움. 예: 202001
"""
import datetime as dt
import json
import os
import sys
import time
import xml.etree.ElementTree as ET
from collections import defaultdict
from pathlib import Path

import requests

TRADE_URL = "https://apis.data.go.kr/1613000/RTMSDataSvcAptTradeDev/getRTMSDataSvcAptTradeDev"
RENT_URL = "https://apis.data.go.kr/1613000/RTMSDataSvcAptRent/getRTMSDataSvcAptRent"

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "out"
STATE = ROOT / "state"
KST = dt.timezone(dt.timedelta(hours=9))

WINDOW_MONTHS = 15      # 거래량: 확정월과 그 전년 동월까지 덮는 기간
RENT_MONTHS = 6         # 전세가율·월세 근거로 쓰는 기간
DEAL_DAYS = 92          # "최근 3개월"
MAX_PRICE = 60000       # 만원 (6억 미만)
MAX_AREA = 85.0         # ㎡ 미만
SUMMARY_DEALS = 60      # summary.md에 싣는 실거래 최대 건수
REPORT_LAG_DAYS = 30    # 실거래 신고기한


class QuotaError(Exception):
    """일일 호출 한도 초과."""


class AuthError(Exception):
    """인증키 문제 — 더 호출해도 소용없으므로 즉시 중단."""


class ApiError(Exception):
    """그 외 API 오류."""


# ---------------------------------------------------------------- 날짜 도우미

def ym_add(ym: str, k: int) -> str:
    y, m = int(ym[:4]), int(ym[4:])
    idx = y * 12 + (m - 1) + k
    return f"{idx // 12:04d}{idx % 12 + 1:02d}"


def ym_range(start: str, end: str):
    cur = start
    while cur <= end:
        yield cur
        cur = ym_add(cur, 1)


def month_end(ym: str) -> dt.date:
    nxt = ym_add(ym, 1)
    return dt.date(int(nxt[:4]), int(nxt[4:]), 1) - dt.timedelta(days=1)


def confirmed_month(today: dt.date) -> str:
    """신고기한(30일)이 지나 건수가 사실상 확정된 가장 최근 계약월."""
    ym = today.strftime("%Y%m")
    while month_end(ym) + dt.timedelta(days=REPORT_LAG_DAYS) >= today:
        ym = ym_add(ym, -1)
    return ym


def fmt_ym(ym: str) -> str:
    return f"{ym[:4]}-{ym[4:]}"


# ---------------------------------------------------------------- API 호출

class Client:
    def __init__(self, key: str):
        self.key = key
        self.s = requests.Session()
        self.calls = 0
        self.errors = []
        self.samples = {}

    def fetch(self, url: str, code: str, ym: str):
        items, page = [], 1
        while True:
            params = {"serviceKey": self.key, "LAWD_CD": code, "DEAL_YMD": ym,
                      "pageNo": page, "numOfRows": 1000}
            text = None
            for attempt in range(4):
                try:
                    r = self.s.get(url, params=params, timeout=40)
                    self.calls += 1
                    text = r.text
                    break
                except requests.RequestException as e:
                    if attempt == 3:
                        raise ApiError(f"{code} {ym}: 네트워크 오류 {type(e).__name__}")
                    time.sleep(3 * (attempt + 1))
            batch, total = self._parse(text, code, ym)
            items.extend(batch)
            if url not in self.samples and batch:
                self.samples[url] = sorted(batch[0].keys())
            if len(items) >= total or not batch:
                return items
            page += 1
            time.sleep(0.05)

    @staticmethod
    def _parse(text: str, code: str, ym: str):
        if "LIMITED_NUMBER_OF_SERVICE_REQUESTS" in text:
            raise QuotaError("일일 호출 한도 초과")
        try:
            root = ET.fromstring(text)
        except ET.ParseError:
            raise ApiError(f"{code} {ym}: XML 아님 — {text[:150]!r}")
        auth = (root.findtext(".//returnAuthMsg") or "").strip()
        if auth:
            if "KEY" in auth or "NOT_REGISTERED" in auth or "UNAUTHORIZED" in auth or "DEADLINE" in auth:
                raise AuthError(auth)
            raise ApiError(f"{code} {ym}: {auth}")
        rc = (root.findtext(".//resultCode") or "").strip()
        if rc not in ("00", "000"):
            msg = (root.findtext(".//resultMsg") or "").strip()
            raise ApiError(f"{code} {ym}: resultCode={rc} {msg}")
        total = int((root.findtext(".//totalCount") or "0").strip() or 0)
        out = []
        for it in root.iter("item"):
            out.append({c.tag: (c.text or "").strip() for c in it})
        return out, total


# ---------------------------------------------------------------- 정규화

def _int(s):
    try:
        return int(str(s).replace(",", "").strip())
    except (TypeError, ValueError):
        return None


def _date(it):
    y, m, d = _int(it.get("dealYear")), _int(it.get("dealMonth")), _int(it.get("dealDay"))
    if not (y and m and d):
        return None
    return f"{y:04d}-{m:02d}-{d:02d}"


def _key(it, code):
    seq = it.get("aptSeq")
    if seq:
        return seq
    return "-".join([it.get("sggCd") or code, it.get("umdNm", ""), it.get("jibun", ""), it.get("aptNm", "")])


def norm_trade(it, code):
    price, date = _int(it.get("dealAmount")), _date(it)
    try:
        area = round(float(it.get("excluUseAr", "")), 2)
    except ValueError:
        area = None
    if price is None or date is None or area is None:
        return None
    gbn = it.get("dealingGbn", "")
    typ = "중개" if "중개" in gbn else ("직거래" if "직" in gbn else "미확인")
    return {
        "key": _key(it, code), "apt": it.get("aptNm", ""), "umd": it.get("umdNm", ""),
        "code": code, "area": area, "price": price, "date": date,
        "floor": it.get("floor", ""), "type": typ,
        "cancelled": it.get("cdealType", "").upper() == "O",
    }


def norm_rent(it, code):
    dep, mon, date = _int(it.get("deposit")), _int(it.get("monthlyRent")), _date(it)
    try:
        area = round(float(it.get("excluUseAr", "")), 2)
    except ValueError:
        area = None
    if dep is None or mon is None or date is None or area is None:
        return None
    return {"key": _key(it, code), "area": area, "deposit": dep, "monthly": mon, "date": date}


def signature(r):
    """시군구 코드와 무관한 거래 식별자. 개편 전후 코드가 같은 거래를 함께 돌려줘도 한 번만 센다."""
    return (r.get("apt", r["key"]), r.get("umd", ""), r["area"], r["date"],
            r.get("price", r.get("deposit")), r.get("floor", ""), r.get("monthly", ""))


def dedupe(rows, seen=None):
    seen = set() if seen is None else seen
    out = []
    for r in rows:
        sig = signature(r)
        if sig not in seen:
            seen.add(sig)
            out.append(r)
    return out


# ---------------------------------------------------------------- 상태 파일

def load_json(path: Path, default):
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return default


def save_json(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=1), encoding="utf-8")


# ---------------------------------------------------------------- 본체

def discover_codes(client, cfg, known, probe_ym, state):
    """행정구역 개편으로 생긴 새 시군구 코드를 한 번 탐색해 state/codes.json에 둔다."""
    codes_state = state.setdefault("discovered", {})
    for prefix, (lo, hi) in cfg["discover_ranges"].items():
        if prefix in codes_state:
            continue
        found = {}
        for n in range(int(lo), int(hi) + 1):
            code = str(n)
            if code in known:
                continue
            try:
                items = client.fetch(TRADE_URL, code, probe_ym)
            except ApiError:  # 없는 코드는 오류로 오기도 한다
                continue
            if items:
                umds = sorted({i.get("umdNm", "") for i in items})
                found[code] = {"count": len(items), "umd": umds[:30]}
        codes_state[prefix] = {"checked": probe_ym, "codes": found}
    return state


def main():
    key = os.environ.get("DATA_GO_KR_KEY", "").strip()
    if not key:
        sys.exit("DATA_GO_KR_KEY가 비어 있습니다. 저장소 Settings → Secrets에 넣어 주세요.")
    cfg = load_json(ROOT / "regions.json", None)
    client = Client(key)
    now = dt.datetime.now(KST)
    today = now.date()
    cur = today.strftime("%Y%m")
    conf = confirmed_month(today)
    prov = ym_add(conf, 1)
    win_start = ym_add(cur, -(WINDOW_MONTHS - 1))
    window = list(ym_range(win_start, cur))
    notes = []

    # 1) 코드 목록
    metro = cfg["metro"]
    known = {c for v in metro.values() for c in v}
    codes_state = load_json(STATE / "codes.json", {})
    try:
        codes_state = discover_codes(client, cfg, known, conf, codes_state)
        save_json(STATE / "codes.json", codes_state)
    except QuotaError:
        notes.append("코드 탐색 중 호출 한도 초과 — 다음 실행에서 이어서 탐색")
    disc = codes_state.get("discovered", {})
    extra = {p: sorted(v["codes"].keys()) for p, v in disc.items()}
    for p, codes in extra.items():
        bucket = "gyeonggi" if p.startswith("41") else "incheon"
        metro[bucket] = sorted(set(metro[bucket]) | set(codes))
    all_codes = sorted({c for v in metro.values() for c in v})

    def region_codes(reg):
        codes = set(reg["codes"])
        if reg.get("discover"):
            codes |= set(extra.get(reg["discover"], []))
        return codes

    watched_codes = sorted({c for r in cfg["watched"] for c in region_codes(r)})

    # 2) 매매. 감시 지역은 15개월 전부, 나머지 수도권 코드는 거래량 비교에 필요한 달만.
    needed = sorted({conf, ym_add(conf, -1), ym_add(conf, -12), prov, ym_add(prov, -12)} & set(window))
    plan = [(c, ym) for c in watched_codes for ym in window]
    plan += [(c, ym) for c in all_codes if c not in watched_codes for ym in needed]

    counts = defaultdict(lambda: defaultdict(int))                                 # code -> ym -> n
    umd_counts = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))        # code -> ym -> umd -> n
    trades = []                                                                    # 감시 지역 거래 원장
    missing = set()                                                                # 받지 못한 (code, ym)
    seen_by_ym = defaultdict(set)
    quota_hit = False
    for i, (code, ym) in enumerate(plan):
        try:
            raw = client.fetch(TRADE_URL, code, ym)
        except QuotaError:
            quota_hit = True
            missing.update(plan[i:])
            notes.append(f"매매 수집 중 호출 한도 초과 — {len(plan) - i}개 지역·월 미수집(표에 '—'로 표시)")
            break
        except ApiError as e:
            client.errors.append(str(e))
            missing.add((code, ym))
            continue
        rows = dedupe([r for r in (norm_trade(x, code) for x in raw) if r], seen_by_ym[ym])
        for r in rows:
            if not r["cancelled"]:
                counts[code][ym] += 1
                umd_counts[code][ym][r["umd"]] += 1
        if code in watched_codes:
            trades.extend(rows)

    # 3) 신고가 이력 (window 이전 기간)
    peaks_state = load_json(STATE / "peaks.json", {"hist_through": None, "hist_from": None, "peaks": {}})
    backfill = os.environ.get("BACKFILL_FROM", "").strip()
    if backfill and (peaks_state["hist_from"] is None or backfill < peaks_state["hist_from"]):
        peaks_state = {"hist_through": ym_add(backfill, -1), "hist_from": backfill, "peaks": {}}
    if peaks_state["hist_through"] is None:
        peaks_state["hist_through"] = ym_add(win_start, -1)
        peaks_state["hist_from"] = win_start
    hist = peaks_state["peaks"]

    def fold_peak(store, r):
        if r["cancelled"] or r["type"] == "직거래":
            return
        k = f'{r["key"]}|{r["area"]}'
        if k not in store or r["price"] > store[k]["price"]:
            store[k] = {"price": r["price"], "date": r["date"], "apt": r["apt"]}

    gap_end = ym_add(win_start, -1)
    if not quota_hit and peaks_state["hist_through"] < gap_end:
        for ym in ym_range(ym_add(peaks_state["hist_through"], 1), gap_end):
            month_rows = []
            try:
                for code in watched_codes:
                    try:
                        raw = client.fetch(TRADE_URL, code, ym)
                    except ApiError as e:
                        client.errors.append(str(e))
                        continue
                    month_rows.extend(r for r in (norm_trade(i, code) for i in raw) if r)
            except QuotaError:
                quota_hit = True
                break
            for r in month_rows:
                fold_peak(hist, r)
            peaks_state["hist_through"] = ym
    # 한도에 걸려도 진행 상황은 남겨 다음 정기 실행이 이어서 채우게 한다
    save_json(STATE / "peaks.json", peaks_state)
    if peaks_state["hist_through"] < gap_end:
        if peaks_state["hist_through"] < peaks_state["hist_from"]:
            done = "아직 시작 못 함"
        else:
            done = f"{fmt_ym(peaks_state['hist_from'])}~{fmt_ym(peaks_state['hist_through'])}까지 채움"
        notes.append(f"신고가 이력 {done} — 나머지는 다음 실행에서 이어 채움. 그동안 신고가 대비 수치는 채운 기간 기준")

    window_peaks = {}
    for r in trades:
        fold_peak(window_peaks, r)

    def peak_of(k):
        a, b = hist.get(k), window_peaks.get(k)
        if a and b:
            return a if a["price"] >= b["price"] else b
        return a or b

    # 4) 전월세 (감시 지역, 최근 6개월)
    rents = []
    if not quota_hit:
        for code in watched_codes:
            for ym in ym_range(ym_add(cur, -(RENT_MONTHS - 1)), cur):
                try:
                    raw = client.fetch(RENT_URL, code, ym)
                except QuotaError:
                    quota_hit = True
                    notes.append("전월세 수집 중 호출 한도 초과")
                    break
                except ApiError as e:
                    client.errors.append(str(e))
                    continue
                rents.extend(r for r in (norm_rent(i, code) for i in raw) if r)
            if quota_hit:
                break
    rents = dedupe(rents)
    if quota_hit and not rents:
        notes.append("전월세는 호출 한도로 이번에 수집하지 못함 — 전세가율·월세 칸이 비어 있음")
    latest_jeonse, latest_wolse = {}, {}
    for r in sorted(rents, key=lambda x: x["date"]):
        k = f'{r["key"]}|{r["area"]}'
        if r["monthly"] == 0:
            latest_jeonse[k] = r
        else:
            latest_wolse[k] = r

    # 5) 지역 소속 판정
    def in_region(reg, r):
        if r["code"] not in region_codes(reg):
            return False
        return not reg.get("umd") or r["umd"] in reg["umd"]

    def total(codes, ym, umd=None):
        """해당 달 건수. 하나라도 못 받은 코드가 있으면 None(0으로 오인하지 않게)."""
        if any((c, ym) in missing for c in codes):
            return None
        if umd:
            return sum(n for c in codes for u, n in umd_counts[c][ym].items() if u in umd)
        return sum(counts[c][ym] for c in codes)

    def pct(a, b):
        return None if a is None or not b else round((a - b) / b * 100, 1)

    def series(get, months):
        c0, cm1, cy1, p0 = get(conf), get(ym_add(conf, -1)), get(ym_add(conf, -12)), get(prov)
        return {"confirmed": c0, "prev": cm1, "yearAgo": cy1, "mom": pct(c0, cm1), "yoy": pct(c0, cy1),
                "provisional": p0, "provisionalYearAgo": get(ym_add(prov, -12)),
                "byMonth": {fmt_ym(ym): get(ym) for ym in months}}

    macro = {}
    for name, codes in metro.items():
        macro[name] = series(lambda ym, cs=codes: total(cs, ym), needed)
    macro["capital"] = series(lambda ym: total(all_codes, ym), needed)

    regions_out = {}
    for reg in cfg["watched"]:
        s = series(lambda ym, rg=reg: total(region_codes(rg), ym, rg.get("umd")), window)
        s.update({"name": reg["name"], "kind": reg["kind"]})
        regions_out[reg["id"]] = s

    # 6) 조건에 맞는 실거래
    cutoff = (today - dt.timedelta(days=DEAL_DAYS)).isoformat()
    by_unit = defaultdict(list)
    for r in trades:
        if not r["cancelled"] and r["type"] != "직거래":
            by_unit[f'{r["key"]}|{r["area"]}'].append(r)
    for v in by_unit.values():
        v.sort(key=lambda x: x["date"])

    deals, seen = [], set()
    for reg in cfg["watched"]:
        for r in trades:
            if (r["cancelled"] or r["type"] == "직거래" or r["date"] < cutoff
                    or r["area"] >= MAX_AREA or r["price"] >= MAX_PRICE or not in_region(reg, r)):
                continue
            sig = (r["key"], r["area"], r["date"], r["price"], r["floor"])
            if sig in seen:
                continue
            seen.add(sig)
            k = f'{r["key"]}|{r["area"]}'
            hist_list = by_unit[k]
            prev = None
            for x in hist_list:
                if (x["date"], x["price"], x["floor"]) == (r["date"], r["price"], r["floor"]):
                    break
                prev = x
            pk = peak_of(k)
            j, w = latest_jeonse.get(k), latest_wolse.get(k)
            deals.append({
                "regionId": reg["id"], "region": reg["name"], "complex": r["apt"], "aptKey": r["key"],
                "umd": r["umd"], "area": r["area"], "price": r["price"], "date": r["date"],
                "floor": r["floor"], "type": r["type"],
                "prevPrice": prev["price"] if prev else None, "prevDate": prev["date"] if prev else None,
                "vsPrev": pct(r["price"], prev["price"]) if prev else None,
                "peakPrice": pk["price"] if pk else None, "peakDate": pk["date"] if pk else None,
                "vsPeak": pct(r["price"], pk["price"]) if pk else None,
                "jeonse": j["deposit"] if j else None, "jeonseDate": j["date"] if j else None,
                "jeonseRatio": round(j["deposit"] / r["price"] * 100, 1) if j else None,
                "monthly": f'{w["deposit"]}/{w["monthly"]}' if w else None,
            })
    deals.sort(key=lambda d: (d["vsPeak"] if d["vsPeak"] is not None else 0, d["date"]))

    # 7) 저장
    meta = {
        "generatedAt": now.strftime("%Y-%m-%d %H:%M KST"),
        "confirmedMonth": fmt_ym(conf), "provisionalMonth": fmt_ym(prov),
        "window": [fmt_ym(window[0]), fmt_ym(window[-1])],
        "peaksSince": fmt_ym(peaks_state["hist_from"]), "peaksThrough": fmt_ym(cur),
        "calls": client.calls, "errors": client.errors[:50], "errorCount": len(client.errors),
        "notes": notes, "discovered": disc, "sampleFields": client.samples,
        "countsBasis": "계약월 기준, 해제 신고 건 제외, 아파트 매매",
    }
    save_json(OUT / "run.json", meta)
    save_json(OUT / "volume.json", {"meta": meta, "macro": macro, "regions": regions_out})
    save_json(OUT / "deals.json", {"meta": meta, "count": len(deals), "deals": deals})
    (OUT / "summary.md").write_text(render_summary(meta, macro, regions_out, deals, cfg, umd_counts, extra, conf),
                                    encoding="utf-8")
    print(f"완료: 호출 {client.calls}건, 오류 {len(client.errors)}건, 실거래 {len(deals)}건")
    for n in notes:
        print("메모:", n)
    if client.calls and len(client.errors) == client.calls:
        sys.exit("모든 호출이 실패했습니다. out/run.json의 errors를 확인하세요.")


# ---------------------------------------------------------------- 요약 문서

def _p(v):
    return "—" if v is None else f"{v:+.1f}%"


def _n(v):
    return "—" if v is None else f"{v:,}"


def render_summary(meta, macro, regions, deals, cfg, umd_counts, extra, conf):
    c, p = meta["confirmedMonth"], meta["provisionalMonth"]
    L = [
        "# 아파트 실거래 수집 요약", "",
        f"생성 {meta['generatedAt']} · 확정월 {c} · 잠정월 {p} · 신고가 기준 {meta['peaksSince']}~",
        f"호출 {meta['calls']:,}건 · 오류 {meta['errorCount']}건 · {meta['countsBasis']}", "",
    ]
    for n in meta["notes"]:
        L.append(f"- 메모: {n}")
    if meta["notes"]:
        L.append("")
    L += ["## 권역", "",
          f"| 권역 | {c} | 전월비 | 전년동월비 | {p} 잠정 | 전년 {p[5:]}월 |",
          "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for k, label in [("capital", "수도권"), ("seoul", "서울"), ("gyeonggi", "경기"), ("incheon", "인천")]:
        s = macro[k]
        L.append(f"| {label} | {_n(s['confirmed'])} | {_p(s['mom'])} | {_p(s['yoy'])} | {_n(s['provisional'])} | {_n(s['provisionalYearAgo'])} |")
    L += ["", "## 감시 지역", "",
          f"| id | 지역 | {c} | 전월비 | 전년동월비 | {p} 잠정 |",
          "| --- | --- | ---: | ---: | ---: | ---: |"]
    for rid, s in regions.items():
        flag = " ⚠" if s["yoy"] is not None and s["yoy"] <= -30 else ""
        L.append(f"| {rid} | {s['name']} | {_n(s['confirmed'])} | {_p(s['mom'])} | {_p(s['yoy'])}{flag} | {_n(s['provisional'])} |")
    L += ["", "⚠ = 전년 동월 대비 30% 이상 감소", "",
          f"## 조건 맞는 실거래 (중개·유형미확인, 85㎡ 미만, 6억 미만, 최근 3개월) — 전체 {len(deals)}건 중 신고가 대비 하락 큰 순 {min(len(deals), SUMMARY_DEALS)}건", "",
          "| 지역 | 단지 | 전용㎡ | 가격(만원) | 계약일 | 유형 | 직전대비 | 신고가(만원) | 신고가대비 | 전세가율 | 월세(보증금/월) |",
          "| --- | --- | ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | --- |"]
    for d in deals[:SUMMARY_DEALS]:
        jr = "—" if d["jeonseRatio"] is None else f"{d['jeonseRatio']}%"
        L.append(f"| {d['region']} | {d['complex']} ({d['umd']}) | {d['area']} | {d['price']:,} | {d['date']} | {d['type']} | "
                 f"{_p(d['vsPrev'])} | {_n(d['peakPrice'])} | {_p(d['vsPeak'])} | {jr} | {d['monthly'] or '—'} |")
    # 행정구역 개편 지역 점검용
    L += ["", "## 개편 지역 점검 (법정동별 확정월 건수)", ""]
    check = [r for r in cfg["watched"] if r.get("umd")]
    for reg in check:
        codes = set(reg["codes"]) | set(extra.get(reg.get("discover", ""), []))
        agg = defaultdict(int)
        for code in codes:
            for u, n in umd_counts[code][conf].items():
                agg[u] += n
        inside = ", ".join(f"{u} {n}" for u, n in sorted(agg.items()) if u in reg["umd"]) or "없음"
        outside = ", ".join(f"{u} {n}" for u, n in sorted(agg.items()) if u not in reg["umd"]) or "없음"
        L.append(f"- {reg['name']} (코드 {', '.join(sorted(codes))}): 포함 {inside} / 제외 {outside}")
    disc = meta["discovered"]
    if disc:
        for pfx, v in disc.items():
            found = ", ".join(f"{k}({x['count']}건)" for k, x in v["codes"].items()) or "새 코드 없음"
            L.append(f"- 코드 탐색 {pfx}*: {found}")
    if meta["sampleFields"]:
        L += ["", "## 응답 필드 확인", ""]
        for url, fields in meta["sampleFields"].items():
            L.append(f"- {url.rsplit('/', 1)[-1]}: {', '.join(fields)}")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    try:
        main()
    except AuthError as e:
        sys.exit(f"인증키 오류: {e}\n키를 등록·승인한 직후라면 1~2시간 뒤 다시 실행하세요. 기존 결과 파일은 그대로 둡니다.")
