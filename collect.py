#!/usr/bin/env python3
"""국토교통부 아파트 매매·전월세 실거래 수집기 (GitHub Actions에서 실행). v2

결과물
  out/summary.md  사람이(그리고 모니터링 작업이) 바로 읽는 요약
  out/volume.json 권역·감시지역별 계약월 거래 건수
  out/deals.json  조건에 맞는 실거래 전체
  out/run.json    실행 정보(호출 수, 오류, 응답 필드 확인용 샘플)
  state/peaks.json 단지·평형별 역대 최고가(직거래·해제 제외)
  state/codes.json 행정구역 개편으로 새로 생긴 시군구 코드 탐색 결과

환경변수
  DATA_GO_KR_KEY  공공데이터포털 일반 인증키(Decoding)
  BACKFILL_FROM   (선택) 신고가 이력을 이 달부터 다시 채움. 예: 202001
"""
import datetime as dt
import json
import os
import statistics
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
MIN_AREA = 30.0         # 이보다 작은 초소형은 잡음이 커서 제외
LARGE_MIN_TRADES = 20   # 15개월 거래 건수로 대단지(약 500세대 이상)를 대신 추정
OUTLIER_PREV = 30.0     # 직전 거래 대비 ±30% 이상이면 '확인' 표시
TARGET_FALL = -15.0     # 신고가 대비 하락 트리거 기준
SUMMARY_DEALS = 60      # summary.md에 싣는 실거래 최대 건수
REPORT_LAG_DAYS = 30    # 실거래 신고기한
PEAK_KEY_VERSION = 3    # 단지 식별 방식을 바꾸면 올린다 (이력 자동 재수집)
MIN_UNITS = 10          # 실거래 변동률을 낼 때 필요한 최소 비교 단지·평형 수


class QuotaError(Exception):
    """일일 호출 한도 초과."""


class AuthError(Exception):
    """인증키 문제(미등록·미승인)."""


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

AUTH_WORDS = ("KEY", "NOT_REGISTERED", "UNAUTHORIZED", "DEADLINE", "서비스키", "인증", "등록되지")


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
            for attempt in range(5):
                try:
                    r = self.s.get(url, params=params, timeout=40)
                    self.calls += 1
                    text = r.text
                    break
                except requests.RequestException as e:
                    if attempt == 4:
                        raise ApiError(f"{code} {ym}: 네트워크 오류 {type(e).__name__}")
                    time.sleep(4 * (attempt + 1))
            batch, total = self._parse(text, code, ym)
            items.extend(batch)
            name = url.rsplit("/", 1)[-1]
            if name not in self.samples and batch:
                self.samples[name] = sorted(batch[0].keys())
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
            if any(w in text for w in AUTH_WORDS):
                raise AuthError(text[:120])
            raise ApiError(f"{code} {ym}: XML 아님 — {text[:150]!r}")
        auth = (root.findtext(".//returnAuthMsg") or "").strip()
        if auth:
            if any(w in auth for w in AUTH_WORDS):
                raise AuthError(auth)
            raise ApiError(f"{code} {ym}: {auth}")
        rc = (root.findtext(".//resultCode") or "").strip()
        if rc not in ("00", "000"):
            msg = (root.findtext(".//resultMsg") or "").strip()
            if any(w in msg for w in AUTH_WORDS):
                raise AuthError(msg)
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


def _area(it):
    try:
        return round(float(it.get("excluUseAr", "")), 2)
    except ValueError:
        return None


def complex_key(apt, jibun, built):
    """시군구 코드·법정동 이름과 무관한 단지 식별자(단지명+지번+준공연도).
    행정구역 개편 전후에도 같은 단지로 이어지고, 이름·지번이 같은 다른 단지와는 준공연도로 갈린다."""
    return f"{apt}|{jibun}|{built}"


def norm_trade(it, code):
    price, date, area = _int(it.get("dealAmount")), _date(it), _area(it)
    if price is None or date is None or area is None:
        return None
    gbn = it.get("dealingGbn", "")
    typ = "중개" if "중개" in gbn else ("직거래" if "직" in gbn else "미확인")
    apt, jibun = it.get("aptNm", ""), it.get("jibun", "")
    return {
        "cx": complex_key(apt, jibun, it.get("buildYear", "")), "apt": apt, "umd": it.get("umdNm", ""),
        "code": code, "area": area, "price": price, "date": date,
        "floor": it.get("floor", ""), "type": typ,
        "cancelled": it.get("cdealType", "").upper() == "O",
    }


def norm_rent(it, code):
    dep, mon, date, area = _int(it.get("deposit")), _int(it.get("monthlyRent")), _date(it), _area(it)
    if dep is None or mon is None or date is None or area is None:
        return None
    apt, jibun = it.get("aptNm", ""), it.get("jibun", "")
    return {"cx": complex_key(apt, jibun, it.get("buildYear", "")), "apt": apt, "umd": it.get("umdNm", ""), "area": area,
            "deposit": dep, "monthly": mon, "date": date, "floor": it.get("floor", "")}


def unit_key(r):
    return f'{r["cx"]}|{r["area"]}'


def signature(r):
    return (r["cx"], r["area"], r["date"], r.get("price", r.get("deposit")), r.get("floor", ""), r.get("monthly", ""))


def dedupe(rows, seen=None):
    """개편 전후 코드가 같은 거래를 함께 돌려줘도 한 번만 센다."""
    seen = set() if seen is None else seen
    out = []
    for r in rows:
        sig = signature(r)
        if sig not in seen:
            seen.add(sig)
            out.append(r)
    return out


def median(vals):
    vals = [v for v in vals if v is not None]
    return round(statistics.median(vals), 1) if vals else None


# ---------------------------------------------------------------- 상태 파일

def load_json(path: Path, default):
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return default


def save_json(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=1), encoding="utf-8")


# ---------------------------------------------------------------- 지역 정의

class Region:
    """codes = 현재 코드. legacy = 개편 전 코드와, 그중 이 지역에 속하는 법정동(None이면 전부)."""

    def __init__(self, d):
        self.id, self.name, self.kind = d["id"], d["name"], d["kind"]
        self.target = bool(d.get("target"))
        self.codes = set(d["codes"])
        lg = d.get("legacy")
        self.legacy_code = lg["code"] if lg else None
        self.legacy_umd = set(lg["umd"]) if lg and lg.get("umd") else None

    @property
    def all_codes(self):
        return self.codes | ({self.legacy_code} if self.legacy_code else set())

    def has(self, r):
        if r["code"] in self.codes:
            return True
        if r["code"] == self.legacy_code:
            return self.legacy_umd is None or r["umd"] in self.legacy_umd
        return False


# ---------------------------------------------------------------- 본체

def discover_codes(client, cfg, known, probe_ym, state):
    """행정구역 개편으로 생긴 새 시군구 코드를 한 번 탐색해 state/codes.json에 둔다."""
    found_all = state.setdefault("discovered", {})
    for prefix, (lo, hi) in cfg["discover_ranges"].items():
        if prefix in found_all:
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
                found[code] = {"count": len(items), "umd": sorted({i.get("umdNm", "") for i in items})[:30]}
        found_all[prefix] = {"checked": probe_ym, "codes": found}
    return state


def main():
    key = os.environ.get("DATA_GO_KR_KEY", "").strip()
    if not key:
        sys.exit("DATA_GO_KR_KEY가 비어 있습니다. 저장소 Settings → Secrets에 넣어 주세요.")
    cfg = load_json(ROOT / "regions.json", None)
    regions = [Region(d) for d in cfg["watched"]]
    client = Client(key)
    now = dt.datetime.now(KST)
    today = now.date()
    cur = today.strftime("%Y%m")
    conf = confirmed_month(today)
    prov = ym_add(conf, 1)
    win_start = ym_add(cur, -(WINDOW_MONTHS - 1))
    window = list(ym_range(win_start, cur))
    notes = []

    # 1) 코드 목록 (수도권 합계용 + 감시 지역)
    metro = cfg["metro"]
    known = {c for v in metro.values() for c in v}
    codes_state = load_json(STATE / "codes.json", {})
    try:
        codes_state = discover_codes(client, cfg, known, conf, codes_state)
        save_json(STATE / "codes.json", codes_state)
    except QuotaError:
        notes.append("코드 탐색 중 호출 한도 초과 — 다음 실행에서 이어서 탐색")
    disc = codes_state.get("discovered", {})
    for p, v in disc.items():
        bucket = "gyeonggi" if p.startswith("41") else "incheon"
        metro[bucket] = sorted(set(metro[bucket]) | set(v["codes"].keys()))
    for reg in regions:  # 감시 지역 코드는 합계에도 반드시 포함
        bucket = "seoul" if any(c.startswith("11") for c in reg.codes) else (
            "incheon" if any(c.startswith("28") for c in reg.codes) else "gyeonggi")
        metro[bucket] = sorted(set(metro[bucket]) | reg.all_codes)
    all_codes = sorted({c for v in metro.values() for c in v})
    watched_codes = sorted({c for r in regions for c in r.all_codes})

    # 2) 매매. 감시 지역은 15개월 전부, 나머지 수도권 코드는 거래량 비교에 필요한 달만.
    needed = sorted({conf, ym_add(conf, -1), ym_add(conf, -12), prov, ym_add(prov, -12)} & set(window))
    plan = [(c, ym) for c in watched_codes for ym in window]
    plan += [(c, ym) for c in all_codes if c not in watched_codes for ym in needed]

    counts = defaultdict(lambda: defaultdict(int))          # code -> ym -> n
    trades = []                                             # 감시 지역 거래 원장
    missing = set()                                         # 받지 못한 (code, ym)
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
        if code in watched_codes:
            trades.extend(rows)

    # 3) 신고가 이력 (window 이전 기간)
    peaks_state = load_json(STATE / "peaks.json", {})
    backfill = os.environ.get("BACKFILL_FROM", "").strip()
    if peaks_state.get("keyVersion") != PEAK_KEY_VERSION:
        old_start = peaks_state.get("hist_from")
        start = old_start or backfill or None
        peaks_state = {"keyVersion": PEAK_KEY_VERSION, "hist_from": start,
                       "hist_through": ym_add(start, -1) if start else None, "peaks": {}}
        if old_start:
            notes.append(f"단지 식별 방식 변경으로 신고가 이력을 {fmt_ym(start)}부터 다시 채움")
    if backfill and (peaks_state["hist_from"] is None or backfill < peaks_state["hist_from"]):
        peaks_state.update({"hist_from": backfill, "hist_through": ym_add(backfill, -1), "peaks": {}})
    if peaks_state["hist_through"] is None:
        peaks_state["hist_through"] = ym_add(win_start, -1)
        peaks_state["hist_from"] = win_start
    hist = peaks_state["peaks"]

    def fold_peak(store, r):
        if r["cancelled"] or r["type"] == "직거래":
            return
        k = unit_key(r)
        if k not in store or r["price"] > store[k]["price"]:
            store[k] = {"price": r["price"], "date": r["date"]}

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
                    month_rows.extend(r for r in (norm_trade(x, code) for x in raw) if r)
            except QuotaError:
                quota_hit = True
                break
            for r in month_rows:
                fold_peak(hist, r)
            peaks_state["hist_through"] = ym
    save_json(STATE / "peaks.json", peaks_state)   # 한도에 걸려도 진행 상황은 남긴다
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

    # 4) 전월세 (감시 지역, 최근 6개월). 이 API만 승인이 안 됐으면 건너뛰고 매매 결과는 살린다.
    rents, rent_status = [], "ok"
    if quota_hit:
        rent_status = "quota"
    else:
        try:
            for code in watched_codes:
                for ym in ym_range(ym_add(cur, -(RENT_MONTHS - 1)), cur):
                    try:
                        raw = client.fetch(RENT_URL, code, ym)
                    except ApiError as e:
                        client.errors.append(str(e))
                        continue
                    rents.extend(r for r in (norm_rent(x, code) for x in raw) if r)
        except AuthError as e:
            rent_status = f"auth: {e}"
        except QuotaError:
            rent_status = "quota"
    rents = dedupe(rents)
    # 마지막으로 받은 전월세를 state/rents.json에 쌓아 두고, 못 받은 회차에는 그 값을 '기존'으로 쓴다
    rent_cache = load_json(STATE / "rents.json", {})
    if rent_cache.get("keyVersion") != PEAK_KEY_VERSION:     # 단지 식별 방식이 바뀌면 캐시를 새로 쌓는다
        rent_cache = {"keyVersion": PEAK_KEY_VERSION, "jeonse": {}, "wolse": {}}
    for r in sorted(rents, key=lambda x: x["date"]):
        kind = "jeonse" if r["monthly"] == 0 else "wolse"
        k = unit_key(r)
        old = rent_cache[kind].get(k)
        if not old or r["date"] >= old["date"]:
            rent_cache[kind][k] = {"deposit": r["deposit"], "monthly": r["monthly"], "date": r["date"]}
    keep_from = (today - dt.timedelta(days=730)).isoformat()   # 2년 넘은 기록은 버린다
    for kind in ("jeonse", "wolse"):
        rent_cache[kind] = {k: v for k, v in rent_cache[kind].items() if v["date"] >= keep_from}
    save_json(STATE / "rents.json", rent_cache)
    rent_fresh = rent_status == "ok"
    if not rent_fresh:
        why = ("전월세 API 인증 실패 — 공공데이터포털에서 「아파트 전월세 실거래가 자료」 활용신청·승인 여부를 확인하세요"
               if rent_status.startswith("auth") else "전월세는 호출 한도로 이번에 수집하지 못함")
        fallback = ("전세가율·월세는 마지막으로 받은 값을 '기존'으로 표시" if rent_cache["jeonse"]
                    else "아직 받은 적이 없어 전세가율·월세 칸이 비어 있음")
        notes.append(f"{why}. {fallback}")
    latest_jeonse, latest_wolse = rent_cache["jeonse"], rent_cache["wolse"]

    # 5) 거래량 집계
    reg_counts = defaultdict(lambda: defaultdict(lambda: {"new": 0, "legacy": 0}))   # region -> ym -> basis -> n
    for r in trades:
        if r["cancelled"]:
            continue
        ym = r["date"][:4] + r["date"][5:7]
        for reg in regions:
            if reg.has(r):
                reg_counts[reg.id][ym]["legacy" if r["code"] == reg.legacy_code else "new"] += 1

    def pct(a, b):
        return None if a is None or not b else round((a - b) / b * 100, 1)

    def metro_total(codes, ym):
        if any((c, ym) in missing for c in codes):
            return None
        return sum(counts[c][ym] for c in codes)

    def region_total(reg, ym):
        if any((c, ym) in missing for c in reg.all_codes):
            return None
        b = reg_counts[reg.id][ym]
        return b["new"] + b["legacy"]

    def basis(reg, ym):
        b = reg_counts[reg.id][ym]
        if not reg.legacy_code:
            return "new"
        return "legacy" if b["legacy"] and not b["new"] else ("new" if b["new"] and not b["legacy"] else "mixed")

    def series(get, months, reg=None):
        c0, cm1, cy1, p0 = get(conf), get(ym_add(conf, -1)), get(ym_add(conf, -12)), get(prov)
        s = {"confirmed": c0, "prev": cm1, "yearAgo": cy1, "mom": pct(c0, cm1), "yoy": pct(c0, cy1),
             "provisional": p0, "provisionalYearAgo": get(ym_add(prov, -12)),
             "byMonth": {fmt_ym(ym): get(ym) for ym in months}}
        if reg is not None and reg.legacy_code:
            s["basis"] = {fmt_ym(ym): basis(reg, ym) for ym in months}
            s["reorgBreak"] = basis(reg, conf) != basis(reg, ym_add(conf, -12))
        return s

    macro = {name: series(lambda ym, cs=codes: metro_total(cs, ym), needed) for name, codes in metro.items()}
    macro["capital"] = series(lambda ym: metro_total(all_codes, ym), needed)

    # 실거래 변동률: 같은 단지·평형의 거래가 중앙값을 두 기간 사이에서 비교하고, 그 변화율들의 중앙값을 낸다
    #   trade3m    최근 3개월(확정월 포함) vs 그 직전 3개월  → 부동산원 '3개월 상승률' 자리를 채우는 실거래 기준 값
    #   tradeTrend 최근 3개월 vs 6~12개월 전               → 추세가 꺾였는지(진입 검토 트리거 후보)
    def ym_of(r):
        return r["date"][:4] + r["date"][5:7]

    recent = set(ym_range(ym_add(conf, -2), conf))
    prev3 = set(ym_range(ym_add(conf, -5), ym_add(conf, -3)))
    base612 = set(ym_range(ym_add(conf, -11), ym_add(conf, -6)))

    def unit_change(rows, a, b):
        by = defaultdict(lambda: ([], []))
        for r in rows:
            m = ym_of(r)
            if m in a:
                by[unit_key(r)][0].append(r["price"])
            elif m in b:
                by[unit_key(r)][1].append(r["price"])
        ch = [statistics.median(x) / statistics.median(y) - 1 for x, y in by.values() if x and y]
        if len(ch) < MIN_UNITS:
            return None, len(ch)
        return round(statistics.median(ch) * 100, 2), len(ch)

    def trade_change(reg):
        rows = [r for r in trades if not r["cancelled"] and r["type"] != "직거래" and reg.has(r)]
        t3, n3 = unit_change(rows, recent, prev3)
        tt, nt = unit_change(rows, recent, base612)
        return {"trade3m": t3, "trade3mUnits": n3, "tradeTrend": tt, "tradeTrendUnits": nt}

    regions_out = {}
    for reg in regions:
        s = series(lambda ym, rg=reg: region_total(rg, ym), window, reg)
        s.update({"name": reg.name, "kind": reg.kind, "target": reg.target})
        s.update(trade_change(reg))
        regions_out[reg.id] = s

    # 6) 조건에 맞는 실거래
    cx_trades = defaultdict(int)
    by_unit = defaultdict(list)
    for r in trades:
        if r["cancelled"]:
            continue
        cx_trades[r["cx"]] += 1
        if r["type"] != "직거래":
            by_unit[unit_key(r)].append(r)
    for v in by_unit.values():
        v.sort(key=lambda x: (x["date"], x["price"]))

    cutoff = (today - dt.timedelta(days=DEAL_DAYS)).isoformat()
    deals, seen = [], set()
    for reg in regions:
        for r in trades:
            if (r["cancelled"] or r["type"] == "직거래" or r["date"] < cutoff
                    or not (MIN_AREA <= r["area"] < MAX_AREA) or r["price"] >= MAX_PRICE
                    or cx_trades[r["cx"]] < LARGE_MIN_TRADES or not reg.has(r)):
                continue
            sig = signature(r)
            if sig in seen:
                continue
            seen.add(sig)
            k = unit_key(r)
            prev = None
            for x in by_unit[k]:
                if signature(x) == sig:
                    break
                prev = x
            pk = peak_of(k)
            rk = window_peaks.get(k)                 # 최근 15개월 최고가 (트리거 기준)
            j, w = latest_jeonse.get(k), latest_wolse.get(k)
            vs_prev = pct(r["price"], prev["price"]) if prev else None
            deals.append({
                "regionId": reg.id, "region": reg.name, "target": reg.target,
                "complex": r["apt"], "umd": r["umd"], "area": r["area"], "price": r["price"],
                "date": r["date"], "floor": r["floor"], "type": r["type"],
                "complexTrades15m": cx_trades[r["cx"]],
                "prevPrice": prev["price"] if prev else None, "prevDate": prev["date"] if prev else None,
                "vsPrev": vs_prev,
                "recentPeakPrice": rk["price"] if rk else None, "recentPeakDate": rk["date"] if rk else None,
                "vsRecent": pct(r["price"], rk["price"]) if rk else None,
                "peakPrice": pk["price"] if pk else None, "peakDate": pk["date"] if pk else None,
                "vsPeak": pct(r["price"], pk["price"]) if pk else None,
                "jeonse": j["deposit"] if j else None, "jeonseDate": j["date"] if j else None,
                "jeonseRatio": round(j["deposit"] / r["price"] * 100, 1) if j else None,
                "jeonseStale": bool(j) and not rent_fresh,
                "monthly": f'{w["deposit"]}/{w["monthly"]}' if w else None,
                "monthlyDate": w["date"] if w else None,
                "check": vs_prev is not None and abs(vs_prev) >= OUTLIER_PREV,
            })
    deals.sort(key=lambda d: (d["vsRecent"] if d["vsRecent"] is not None else 0, d["date"]))

    deal_stats = {}
    for reg in regions:
        ds = [d for d in deals if d["regionId"] == reg.id and not d["check"]]
        deal_stats[reg.id] = {
            "name": reg.name, "target": reg.target, "n": len(ds),
            "vsRecentMedian": median(d["vsRecent"] for d in ds),
            "fallOver15": sum(1 for d in ds if d["vsRecent"] is not None and d["vsRecent"] <= TARGET_FALL),
            "vsPeakMedian": median(d["vsPeak"] for d in ds),
            "fallOver15AllTime": sum(1 for d in ds if d["vsPeak"] is not None and d["vsPeak"] <= TARGET_FALL),
            "jeonseRatioMedian": median(d["jeonseRatio"] for d in ds),
            "jeonseStale": not rent_fresh,
        }

    # 7) 저장
    meta = {
        "generatedAt": now.strftime("%Y-%m-%d %H:%M KST"),
        "confirmedMonth": fmt_ym(conf), "provisionalMonth": fmt_ym(prov),
        "window": [fmt_ym(window[0]), fmt_ym(window[-1])],
        "peaksSince": fmt_ym(peaks_state["hist_from"]), "peaksThrough": fmt_ym(peaks_state["hist_through"]),
        "calls": client.calls, "errors": client.errors[:50], "errorCount": len(client.errors),
        "rentStatus": rent_status, "notes": notes, "discovered": disc, "sampleFields": client.samples,
        "countsBasis": "계약월 기준, 해제 신고 건 제외, 아파트 매매",
        "dealFilter": (f"중개·유형미확인, 전용 {MIN_AREA:.0f}~{MAX_AREA:.0f}㎡ 미만, {MAX_PRICE // 10000}억 미만, "
                       f"최근 {DEAL_DAYS}일, 15개월 거래 {LARGE_MIN_TRADES}건 이상 단지(대단지 추정)"),
    }
    save_json(OUT / "run.json", meta)
    save_json(OUT / "volume.json", {"meta": meta, "macro": macro, "regions": regions_out})
    save_json(OUT / "deals.json", {"meta": meta, "count": len(deals), "stats": deal_stats, "deals": deals})
    (OUT / "summary.md").write_text(render_summary(meta, macro, regions_out, deals, deal_stats), encoding="utf-8")
    print(f"완료: 호출 {client.calls}건, 오류 {len(client.errors)}건, 실거래 {len(deals)}건, 전월세 {rent_status}")
    for n in notes:
        print("메모:", n)


# ---------------------------------------------------------------- 요약 문서

def _p(v):
    return "—" if v is None else f"{v:+.1f}%"


def _n(v):
    return "—" if v is None else f"{v:,}"


def render_summary(meta, macro, regions, deals, stats):
    c, p = meta["confirmedMonth"], meta["provisionalMonth"]
    c_prev_year = f"{int(c[:4]) - 1}{c[4:]}"
    L = [
        "# 아파트 실거래 수집 요약", "",
        f"생성 {meta['generatedAt']} · 확정월 {c} · 잠정월 {p} · 신고가 기준 {meta['peaksSince']}~",
        f"호출 {meta['calls']:,}건 · 오류 {meta['errorCount']}건 · 전월세 {meta['rentStatus']} · {meta['countsBasis']}", "",
    ]
    for n in meta["notes"]:
        L.append(f"- 메모: {n}")
    if meta["notes"]:
        L.append("")
    L += ["## 권역 거래량", "",
          f"| 권역 | {c} | 전월비 | 전년동월비 | {p} 잠정 | 전년 {p[5:]}월 |",
          "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for k, label in [("capital", "수도권"), ("seoul", "서울"), ("gyeonggi", "경기"), ("incheon", "인천")]:
        s = macro[k]
        L.append(f"| {label} | {_n(s['confirmed'])} | {_p(s['mom'])} | {_p(s['yoy'])} | {_n(s['provisional'])} | {_n(s['provisionalYearAgo'])} |")
    L += ["", "## 감시 지역 거래량", "",
          f"| id | 지역 | 목표 | {c} | 전월비 | 전년동월비 | {p} 잠정 | 실거래 3개월 | 실거래 추세(6~12개월 전 대비) |",
          "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for rid, s in regions.items():
        flag = " ⚠" if s["yoy"] is not None and s["yoy"] <= -30 else ""
        brk = " †" if s.get("reorgBreak") else ""
        L.append(f"| {rid} | {s['name']} | {'●' if s['target'] else ''} | {_n(s['confirmed'])} | {_p(s['mom'])} | "
                 f"{_p(s['yoy'])}{flag}{brk} | {_n(s['provisional'])} | {_p(s.get('trade3m'))} | {_p(s.get('tradeTrend'))} |")
    L += ["", "⚠ 전년 동월 대비 30% 이상 감소 · † 행정구역 개편 전후 비교(참고용) · ● 목표 지역(규제지역·지정 임박 후보)",
          f"실거래 3개월 = 같은 단지·평형의 최근 3개월({c}까지) 거래가 중앙값을 직전 3개월과 비교한 변화율의 중앙값. "
          f"실거래 추세 = 최근 3개월을 6~12개월 전과 비교. 비교 가능한 단지·평형이 {MIN_UNITS}개 미만이면 —.", "",
          "## 지역별 실거래 요약", "",
          f"조건: {meta['dealFilter']}. '확인' 표시 거래(직전 대비 ±30% 이상)는 중앙값에서 뺌. "
          "최근최고 = 최근 15개월 최고가(트리거 기준), 역대최고 = 2020년 이후 최고가(참고).", "",
          "| id | 지역 | 목표 | 건수 | 최근최고 대비 중앙값 | 최근최고 대비 -15% 이상 건수 | 역대최고 대비 중앙값 | 전세가율 중앙값 |",
          "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |"]
    for rid, s in stats.items():
        jr = "—" if s["jeonseRatioMedian"] is None else f"{s['jeonseRatioMedian']}%" + (" (기존)" if s["jeonseStale"] else "")
        L.append(f"| {rid} | {s['name']} | {'●' if s['target'] else ''} | {s['n']:,} | {_p(s['vsRecentMedian'])} | "
                 f"{s['fallOver15']:,} | {_p(s['vsPeakMedian'])} | {jr} |")
    tdeals = [d for d in deals if d["target"]]
    L += ["", f"## 목표 지역 실거래 — 최근 15개월 최고가 대비 하락 큰 순 {min(len(tdeals), SUMMARY_DEALS)}건 (목표 지역 전체 {len(tdeals):,}건)", "",
          "| 지역 | 단지 | 전용㎡ | 가격(만원) | 계약일 | 유형 | 직전대비 | 최근최고(만원) | 최근최고 대비 | 역대최고(만원) | 역대최고 대비 | 전세가율 | 월세(보증금/월) | 비고 |",
          "| --- | --- | ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |"]
    for d in tdeals[:SUMMARY_DEALS]:
        if d["jeonseRatio"] is None:
            jr = "—"
        else:
            jr = f"{d['jeonseRatio']}%" + (f" (기존 {d['jeonseDate'][:7]})" if d["jeonseStale"] else "")
        L.append(f"| {d['region']} | {d['complex']} ({d['umd']}) | {d['area']} | {d['price']:,} | {d['date']} | {d['type']} | "
                 f"{_p(d['vsPrev'])} | {_n(d['recentPeakPrice'])} | {_p(d['vsRecent'])} | {_n(d['peakPrice'])} | {_p(d['vsPeak'])} | "
                 f"{jr} | {d['monthly'] or '—'} | {'확인' if d['check'] else ''} |")
    breaks = [(rid, s) for rid, s in regions.items() if "basis" in s]
    if breaks:
        L += ["", "## 개편 지역 집계 기준", ""]
        for rid, s in breaks:
            months = list(s["basis"].items())
            first_new = next((m for m, b in months if b in ("new", "mixed")), None)
            when = f"{first_new}부터 새 코드" if first_new else "아직 옛 코드"
            L.append(f"- {s['name']}: {when}, 그 전은 옛 코드의 해당 법정동으로 집계. "
                     f"확정월 {c}={s['basis'].get(c, '—')}, 전년 동월 {c_prev_year}={s['basis'].get(c_prev_year, '—')}")
    if meta["sampleFields"]:
        L += ["", "## 응답 필드 확인", ""]
        for name, fields in meta["sampleFields"].items():
            L.append(f"- {name}: {', '.join(fields)}")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    try:
        main()
    except AuthError as e:
        sys.exit(f"인증키 오류: {e}\n키를 등록·승인한 직후라면 1~2시간 뒤 다시 실행하세요. 기존 결과 파일은 그대로 둡니다.")
