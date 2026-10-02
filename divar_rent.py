#!/usr/bin/env python3
"""
divar_rent.py — کرال آگهی‌های اجاره دیوار، یکی‌کردن آگهی‌های تکراری
و نمایش ارزان‌ترین نسخه‌ی هر خانه.

اجرا:
    pip install requests pillow
    python divar_rent.py                  # یک بار اجرا
    python divar_rent.py --loop 30        # هر ۳۰ دقیقه یک بار

نکته: از endpointهای عمومی وب‌اپ divar.ir استفاده می‌کند (همان‌هایی که سایت
خودش صدا می‌زند). این endpointها غیررسمی‌اند و ممکن است تغییر کنند.
فقط برای استفاده‌ی شخصی و با سرعت کم اجرا کنید.
"""

from __future__ import annotations

import argparse
import html
import io
import json
import os
import re
import sqlite3
import sys
import time
from datetime import datetime
from pathlib import Path
from urllib.parse import parse_qs, unquote, urlsplit

import requests

try:
    from PIL import Image
except ImportError:  # بدون Pillow، مقایسه‌ی عکس غیرفعال می‌شود
    Image = None

API = "https://api.divar.ir"
WEB = "https://divar.ir"
PAGINATION_TYPE = "type.googleapis.com/post_list.PaginationData"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")

# شناسه‌ی شهرها در دیوار (از پروژه‌ی MIT به نام divar-mcp)
CITY_SLUGS = {
    "tehran": "1", "karaj": "2", "mashhad": "3", "isfahan": "4", "tabriz": "5",
    "shiraz": "6", "ahvaz": "7", "qom": "8", "kermanshah": "9", "urmia": "10",
    "zahedan": "11", "rasht": "12", "kerman": "13", "hamedan": "14", "arak": "15",
    "yazd": "16", "ardabil": "17", "bandar-abbas": "18", "qazvin": "19", "zanjan": "20",
}

DEFAULT_CONFIG = {
    "search_urls": [],
    "max_pages": 5,
    "request_interval_seconds": 2.0,
    "conversion_rate_monthly": 0.03,
    "detail_refresh_hours": 12,
    "max_images_per_post": 5,
    "filters": {
        "max_deposit": None, "max_rent": None, "max_monthly_cost": None,
        "min_area": None, "max_area": None, "min_rooms": None,
    },
    "exclude_terms": ["همخانه", "هم خانه", "خوابگاه"],
    "exclude_agencies": False,
    "min_plausible_monthly_cost": 1_000_000,
    "report_path": "report.html",
    "db_path": "divar_rent.db",
    "telegram": {"bot_token": "", "chat_id": "", "max_photos": 4},
}

# ------------------------------------------------------------------ متن و عدد

_FA = "۰۱۲۳۴۵۶۷۸۹"
_AR = "٠١٢٣٤٥٦٧٨٩"
_DIGITS = {ord(c): str(i) for i, c in enumerate(_FA)}
_DIGITS.update({ord(c): str(i) for i, c in enumerate(_AR)})


def en_digits(s) -> str:
    return str(s or "").translate(_DIGITS)


def fa_digits(s) -> str:
    return "".join(_FA[int(c)] if c.isdigit() else c for c in str(s))


def norm_text(s: str) -> str:
    s = en_digits(s).replace("ي", "ی").replace("ك", "ک").replace("ة", "ه")
    s = s.replace("\u200c", " ").replace("ـ", "")
    s = re.sub(r"[\u064B-\u065F\u0670\u0654]", "", s)
    s = re.sub(r"[^\w\s]", " ", s.lower())
    return re.sub(r"\s+", " ", s).strip()


def norm_key(s: str) -> str:
    return re.sub(r"[\s\u200c\u0654ٔ]", "", str(s or "")).replace("ي", "ی")


def parse_amount(text) -> int | None:
    """'۵۰۰٬۰۰۰٬۰۰۰ تومان' / '۱٫۵ میلیارد' / 'مجانی' → عدد به تومان (None یعنی توافقی/نامعلوم)."""
    if text is None:
        return None
    if isinstance(text, (int, float)):
        return int(text)
    t = en_digits(text).replace("\u200c", " ")
    if any(w in t for w in ("مجانی", "رایگان")):
        return 0
    t = t.replace("٫", ".").replace("٬", "").replace(",", "").replace("،", "")
    m = re.search(r"\d+(?:\.\d+)?", t.replace(" ", ""))
    if not m:
        return None
    value = float(m.group())
    if "میلیارد" in t:
        value *= 1_000_000_000
    elif "میلیون" in t:
        value *= 1_000_000
    elif "هزار" in t:
        value *= 1_000
    return int(value)


ROOM_WORDS = {"بدون اتاق": 0, "یک": 1, "دو": 2, "سه": 3, "چهار": 4, "پنج": 5}


def parse_rooms(v) -> int | None:
    t = str(v or "").strip()
    for word, n in ROOM_WORDS.items():
        if t.startswith(word):
            return n
    m = re.search(r"\d+", en_digits(t))
    return int(m.group()) if m else None


def parse_floor(v) -> int | None:
    t = en_digits(v)
    if "زیر" in t:
        return -1
    if "همکف" in t:
        return 0
    m = re.search(r"-?\d+", t)
    return int(m.group()) if m else None


def money(x) -> str:
    if x is None:
        return "توافقی"
    if x == 0:
        return "۰"
    if x >= 1_000_000_000:
        s = f"{x / 1_000_000_000:.2f}".rstrip("0").rstrip(".") + " میلیارد"
    elif x >= 1_000_000:
        s = f"{x / 1_000_000:.1f}".rstrip("0").rstrip(".") + " میلیون"
    else:
        s = f"{x:,}"
    return fa_digits(s)


# ------------------------------------------------------------------ HTTP

class Divar:
    def __init__(self, interval: float):
        self.interval = interval
        self.last = 0.0
        self.s = requests.Session()
        self.s.headers.update({
            "user-agent": UA, "accept": "application/json, text/plain, */*",
            "accept-language": "fa-IR,fa;q=0.9", "origin": WEB, "referer": WEB + "/",
        })

    def _wait(self, interval=None):
        gap = (interval if interval is not None else self.interval) - (time.time() - self.last)
        if gap > 0:
            time.sleep(gap)
        self.last = time.time()

    def _call(self, method, url, **kw):
        for attempt in range(4):
            self._wait()
            try:
                r = self.s.request(method, url, timeout=30, **kw)
            except requests.RequestException as e:
                err = e
            else:
                if r.status_code == 429 or r.status_code >= 500:
                    err = RuntimeError(f"HTTP {r.status_code}")
                else:
                    return r
            time.sleep(5 * (attempt + 1))
        raise RuntimeError(f"دسترسی به دیوار ممکن نشد: {err}")

    def search(self, body: dict) -> dict:
        r = self._call("POST", API + "/v8/postlist/w/search", json=body)
        if r.status_code >= 400:
            raise ValueError(f"HTTP {r.status_code}: {r.text[:300]}")
        return r.json()

    def count(self, body: dict) -> int | None:
        """تعداد تقریبی آگهی‌های جست‌وجو (همان عددی که سایت روی دکمه‌ی «نمایش … آگهی» نشان می‌دهد)."""
        try:
            r = self._call("POST", API + "/v8/postlist/w/approximate-post-count", json=body)
            return int(r.json()["count"]) if r.ok else None
        except Exception:
            return None

    def detail(self, token: str) -> dict:
        r = self._call("GET", f"{API}/v8/posts-v2/web/{token}")
        r.raise_for_status()
        return r.json()

    def image(self, url: str) -> bytes | None:
        try:
            self._wait(0.3)
            r = self.s.get(url, timeout=20)
            return r.content if r.ok else None
        except requests.RequestException:
            return None


# ------------------------------------------------------------------ URL → درخواست جست‌وجو

SKIP_PARAMS = {"map_bbox", "map_place_hash", "map_interacted", "page"}
CORE_KEYS = {"category", "districts", "bbox"}

# نام دسته در آدرس سایت با نامش در API فرق دارد؛ بقیه‌ی دسته‌ها همان‌طور فرستاده می‌شوند.
CATEGORY_SLUGS = {
    "rent-residential": "residential-rent",
    "rent-apartment": "apartment-rent",
    "rent-villa": "house-villa-rent",
}


def url_to_body(url: str) -> tuple[dict, list[str]]:
    """آدرس صفحه‌ی جست‌وجوی دیوار را (با فیلترهایش) به بدنه‌ی درخواست API تبدیل می‌کند."""
    warnings = []
    parts = urlsplit(url)
    path = [unquote(p) for p in parts.path.split("/") if p]
    if not path or path[0] != "s" or len(path) < 3:
        raise ValueError(f"آدرس جست‌وجوی دیوار نیست: {url}")
    city_slug, category = path[1], path[2]
    qs = {k: v[0] for k, v in parse_qs(parts.query).items()}

    city_ids = []
    if "cities" in qs:
        city_ids = [c for c in qs.pop("cities").split(",") if c]
    elif city_slug in CITY_SLUGS:
        city_ids = [CITY_SLUGS[city_slug]]
    else:
        raise ValueError(f"شهر «{city_slug}» شناخته نشد؛ در دیوار شهر را انتخاب کن تا "
                         "پارامتر cities در آدرس بیاید، یا آن را به CITY_SLUGS اضافه کن.")
    if len(path) > 3:
        warnings.append(f"محله‌ی «{path[3]}» داخل مسیر آدرس است و اعمال نمی‌شود؛ "
                        "محله‌ها را از فیلتر «محله» انتخاب کن تا به صورت districts= در آدرس بیایند.")

    data = {"category": {"str": {"value": CATEGORY_SLUGS.get(category, category)}}}
    query = qs.pop("q", None)
    for key, val in qs.items():
        if key in SKIP_PARAMS or key.startswith("map_"):
            continue
        if key == "bbox":  # محدوده‌ی کشیده‌شده روی نقشه: طول و عرض جغرافیایی دو گوشه
            data[key] = {"repeated_float": {"value": [{"value": float(v)} for v in val.split(",")]}}
        elif key == "districts" or re.fullmatch(r"[\d,]+", val) and "," in val:
            data[key] = {"repeated_string": {"value": [v for v in val.split(",") if v]}}
        elif re.fullmatch(r"-?\d*-\d*|\d+-", val) and "-" in val:
            lo, _, hi = val.partition("-") if not val.startswith("-") else ("", "-", val[1:])
            rng = {}
            if lo:
                rng["minimum"] = int(lo)
            if hi:
                rng["maximum"] = int(hi)
            data[key] = {"number_range": rng}
        elif val == "true":
            data[key] = {"boolean": {}}
        else:
            data[key] = {"repeated_string": {"value": val.split(",")}}

    body = {"city_ids": city_ids, "search_data": {"form_data": {"data": data}}}
    if query:
        body["search_data"]["query"] = query
    return body, warnings


def iter_search(dv: Divar, body: dict, max_pages: int):
    cursor = None
    for page in range(1, max_pages + 1):
        b = json.loads(json.dumps(body))
        b["pagination_data"] = {"@type": PAGINATION_TYPE, "page": page, "page_size": 24, **(cursor or {})}
        try:
            resp = dv.search(b)
        except ValueError as e:
            # اگر API فیلتری را نپذیرفت، فقط با دسته و محله دوباره تلاش کن؛
            # بقیه‌ی فیلترها سمت ما (بخش filters در config) اعمال می‌شوند.
            data = body["search_data"]["form_data"]["data"]
            if set(data) - CORE_KEYS:
                print(f"  ! API فیلترها را نپذیرفت ({e}). جست‌وجو فقط با دسته و محله ادامه پیدا می‌کند.")
                body["search_data"]["form_data"]["data"] = {k: v for k, v in data.items() if k in CORE_KEYS}
                yield from iter_search(dv, body, max_pages - page + 1)
                return
            raise
        for w in resp.get("list_widgets", []):
            if w.get("widget_type") == "POST_ROW":
                yield w.get("data") or {}
        pag = resp.get("pagination") or {}
        if not pag.get("has_next_page") or not pag.get("data"):
            return
        cursor = {k: v for k, v in pag["data"].items() if k not in ("@type", "search_uid", "viewed_tokens")}


# ------------------------------------------------------------------ تجزیه‌ی آگهی

def row_info(row: dict) -> dict:
    payload = (row.get("action") or {}).get("payload") or {}
    web = payload.get("web_info") or {}
    texts = [row.get(k) or "" for k in ("top_description_text", "middle_description_text", "bottom_description_text")]
    return {
        "token": row.get("token") or payload.get("token"),
        "title": (row.get("title") or "").strip(),
        "district": web.get("district_persian") or "",
        "row_texts": texts,
        "sig": "|".join([row.get("title") or ""] + texts[:2]),
        "thumb": row.get("image_url"),
    }


def _walk(obj):
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from _walk(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _walk(v)


def parse_detail(p: dict) -> dict:
    out = {"description": "", "attrs": {}, "features": [], "images": [], "photos": [], "district_id": None,
           "business_type": (p.get("webengage") or {}).get("business_type")}
    for sec in p.get("sections", []):
        for w in sec.get("widgets", []):
            wt, d = w.get("widget_type"), w.get("data") or {}
            if wt == "LEGEND_TITLE_ROW" and d.get("title"):
                out["title"] = d["title"]
            elif wt == "DESCRIPTION_ROW":
                out["description"] = d.get("text") or ""
            elif wt == "GROUP_INFO_ROW":
                for it in d.get("items") or []:
                    if it.get("title"):
                        out["attrs"][norm_key(it["title"])] = it.get("value")
            elif wt == "GROUP_FEATURE_ROW":
                out["features"] += [it.get("title") for it in d.get("items") or [] if it.get("title")]
            elif d.get("title") and d.get("value") is not None:
                out["attrs"][norm_key(d["title"])] = d.get("value")
            if sec.get("section_name") == "IMAGE":
                for it in d.get("items") or []:
                    img = it.get("image") or {}
                    if img.get("url"):
                        out["images"].append(img.get("thumbnail_url") or img["url"])
                        out["photos"].append(img["url"])  # اندازه‌ی اصلی، برای تلگرام
            if sec.get("section_name") == "TAGS":
                for chip in ((d.get("chip_list") or {}).get("chips") or []):
                    form = (((chip.get("action") or {}).get("payload") or {}).get("search_data") or {}).get("form_data") or {}
                    ids = (((form.get("data") or {}).get("districts") or {}).get("repeated_string") or {}).get("value")
                    if ids and not out["district_id"]:
                        out["district_id"] = ids[0]
    out["convertible"] = "قابل تبدیل" in json.dumps(p, ensure_ascii=False)
    # آخرین راه: هر ویجتی که هم credit و هم rent دارد
    out["slider"] = None
    for d in _walk(p):
        if "credit" in d and "rent" in d:
            c, r = d["credit"], d["rent"]
            c = c.get("value") if isinstance(c, dict) else c
            r = r.get("value") if isinstance(r, dict) else r
            out["slider"] = (parse_amount(c), parse_amount(r))
            break
    return out


def _attr(attrs: dict, *needles):
    for k, v in attrs.items():
        if any(n in k for n in needles):
            return v
    return None


def _amount_attr(attrs: dict, *needles):
    for k, v in attrs.items():
        if any(n in k for n in needles):
            amount = parse_amount(v)
            if amount is not None:
                return amount
    return None


def build_listing(info: dict, det: dict) -> dict:
    a = det.get("attrs", {})
    deposit = _amount_attr(a, "ودیعه", "رهن")
    rent = _amount_attr(a, "اجاره")
    if (deposit is None or rent is None) and det.get("slider"):
        deposit = deposit if deposit is not None else det["slider"][0]
        rent = rent if rent is not None else det["slider"][1]
    for t in info.get("row_texts", []):  # متن ردیف لیست، اگر جزئیات چیزی نداد
        if deposit is None and ("ودیعه" in t or "رهن" in t):
            deposit = parse_amount(t)
        if rent is None and "اجاره" in t:
            rent = parse_amount(t)
    area = _amount_attr(a, "متراژ")
    year = _amount_attr(a, "ساخت")
    floor_raw = _attr(a, "طبقه")
    return {
        "token": info["token"],
        "url": f"{WEB}/v/{info['token']}",
        "title": det.get("title") or info["title"],
        "district": info.get("district") or "",
        "district_id": det.get("district_id"),
        "description": det.get("description", ""),
        "deposit": deposit, "rent": rent,
        "convertible": det.get("convertible", False),
        "area": area, "rooms": parse_rooms(_attr(a, "اتاق")),
        "year": year if year and 1300 < year < 1500 else None,
        "floor": parse_floor(floor_raw) if floor_raw is not None else None,
        "features": det.get("features", []),
        "agency": bool(det.get("business_type")) and det.get("business_type") != "personal",
        "images": det.get("images", []) or ([info["thumb"]] if info.get("thumb") else []),
        "photos": det.get("photos", []),
        "img_hashes": [],
    }


# ------------------------------------------------------------------ تشخیص تکراری

def dhash(data: bytes) -> int | None:
    if Image is None or not data:
        return None
    try:
        im = Image.open(io.BytesIO(data)).convert("L").resize((9, 8), Image.LANCZOS)
    except Exception:
        return None
    px = list(im.getdata())
    bits = 0
    for row in range(8):
        for col in range(8):
            bits = (bits << 1) | (px[row * 9 + col] > px[row * 9 + col + 1])
    return bits


def hamming(a: int, b: int) -> int:
    return bin(a ^ b).count("1")


def shingles(text: str) -> set:
    w = norm_text(text).split()
    return set(zip(w, w[1:], w[2:])) if len(w) >= 3 else set(w)


def jaccard(a: set, b: set) -> float:
    return len(a & b) / len(a | b) if a and b else 0.0


def same_house(x: dict, y: dict, sx: set, sy: set) -> bool:
    hx, hy = x["img_hashes"], y["img_hashes"]
    shared = sum(1 for h in hx if any(hamming(h, g) <= 6 for g in hy)) if hx and hy else 0
    if shared >= 3:
        return True

    def known(k):
        return x.get(k) is not None and y.get(k) is not None

    if known("floor") and x["floor"] != y["floor"]:
        return False
    if known("rooms") and x["rooms"] != y["rooms"]:
        return False
    if known("year") and abs(x["year"] - y["year"]) > 1:
        return False
    area_close = known("area") and abs(x["area"] - y["area"]) <= max(2, 0.03 * x["area"])
    area_conflict = known("area") and not area_close
    if area_conflict and shared < 2:
        return False
    text = jaccard(sx, sy)
    struct = area_close and known("rooms") and (known("year") or known("floor"))
    return (shared >= 2
            or (shared >= 1 and (area_close or text >= 0.3))
            or (struct and text >= 0.25)
            or (text >= 0.6 and (area_close or not known("area"))))


def cluster(listings: list[dict]) -> list[list[dict]]:
    parent = list(range(len(listings)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    sh = [shingles(l["title"] + " " + l["description"]) for l in listings]
    # جفت‌های کاندید: عکس مشترک (با ایندکس باند) یا متراژ نزدیک
    cand = set()
    bands: dict = {}
    for i, l in enumerate(listings):
        for h in l["img_hashes"]:
            for b in range(8):  # فاصله‌ی ≤۷ یعنی دست‌کم یک بایت عیناً یکی است
                bands.setdefault((b, (h >> (8 * b)) & 0xFF), set()).add(i)
    for members in bands.values():
        if len(members) < 40:  # بایت‌های خیلی رایج اطلاعاتی ندارند
            m = sorted(members)
            cand.update((a, b) for k, a in enumerate(m) for b in m[k + 1:])
    by_area = sorted((l["area"], i) for i, l in enumerate(listings) if l["area"])
    for k, (ar, i) in enumerate(by_area):
        for ar2, j in by_area[k + 1:]:
            if ar2 - ar > max(2, 0.03 * ar):
                break
            cand.add((min(i, j), max(i, j)))
    no_area = [i for i, l in enumerate(listings) if not l["area"]]
    cand.update((min(i, j), max(i, j)) for i in no_area for j in range(len(listings)) if i != j)

    for i, j in cand:
        if find(i) != find(j) and same_house(listings[i], listings[j], sh[i], sh[j]):
            parent[find(i)] = find(j)
    groups: dict = {}
    for i, l in enumerate(listings):
        groups.setdefault(find(i), []).append(l)
    return list(groups.values())


# ------------------------------------------------------------------ قیمت

def monthly_cost(l: dict, rate: float) -> int | None:
    if l["deposit"] is None and l["rent"] is None:
        return None
    return int((l["rent"] or 0) + (l["deposit"] or 0) * rate)


def pick_best(group: list[dict], cfg: dict) -> tuple[dict, bool]:
    rate, floor_cost = cfg["conversion_rate_monthly"], cfg["min_plausible_monthly_cost"]
    for l in group:
        l["cost"] = monthly_cost(l, rate)
        l["suspicious"] = l["cost"] is None or l["cost"] < floor_cost
    ok = [l for l in group if not l["suspicious"]]
    if ok:
        return min(ok, key=lambda l: l["cost"]), False
    return group[0], True


def passes_filters(l: dict, cfg: dict) -> bool:
    f = cfg.get("filters") or {}
    text = norm_text(l["title"] + " " + l["description"])
    if any(norm_text(t) in text for t in cfg.get("exclude_terms", [])):
        return False
    if cfg.get("exclude_agencies") and l["agency"]:
        return False
    checks = [("max_deposit", l["deposit"], lambda v, lim: v <= lim),
              ("max_rent", l["rent"], lambda v, lim: v <= lim),
              ("max_monthly_cost", l.get("cost"), lambda v, lim: v <= lim),
              ("min_area", l["area"], lambda v, lim: v >= lim),
              ("max_area", l["area"], lambda v, lim: v <= lim),
              ("min_rooms", l["rooms"], lambda v, lim: v >= lim)]
    return all(f.get(k) is None or v is None or ok(v, f[k]) for k, v, ok in checks)


# ------------------------------------------------------------------ پایگاه داده

def open_db(path: str) -> sqlite3.Connection:
    db = sqlite3.connect(path)
    db.executescript("""
        CREATE TABLE IF NOT EXISTS posts(token TEXT PRIMARY KEY, data TEXT, sig TEXT,
            first_seen REAL, last_seen REAL, detail_at REAL, run INTEGER);
        CREATE TABLE IF NOT EXISTS notified(token TEXT PRIMARY KEY, best_cost INTEGER, at REAL);
        CREATE TABLE IF NOT EXISTS runs(id INTEGER PRIMARY KEY AUTOINCREMENT, at REAL);
    """)
    return db


# ------------------------------------------------------------------ گزارش HTML

CSS = """
:root{--paper:#F3F5F4;--ink:#1D2B33;--muted:#5E6F78;--line:#D5DDDF;--brand:#2E5E6E;--new:#B4532A;--card:#fff}
@media (prefers-color-scheme:dark){:root{--paper:#131A1E;--ink:#E3EAED;--muted:#93A4AC;--line:#2A363C;--brand:#7FB3C2;--new:#E08A5F;--card:#1A2328}}
*{box-sizing:border-box}body{margin:0;background:var(--paper);color:var(--ink);
font-family:Vazirmatn,"Vazir",Tahoma,"Segoe UI",sans-serif;line-height:1.7}
main{max-width:860px;margin:0 auto;padding:28px 16px 60px}
h1{font-size:1.6rem;margin:0 0 4px}.sub{color:var(--muted);margin:0 0 24px;font-size:.92rem}
.house{display:grid;grid-template-columns:120px 1fr auto;gap:16px;align-items:start;
background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px;margin-bottom:12px}
.house img{width:120px;height:90px;object-fit:cover;border-radius:6px;background:var(--line)}
.house h2{font-size:1rem;margin:0 0 2px}.house h2 a{color:inherit;text-decoration:none}
.house h2 a:hover,.house h2 a:focus-visible{text-decoration:underline;outline:none}
.facts{color:var(--muted);font-size:.86rem;margin:0}
.cost{text-align:left;white-space:nowrap}.cost b{display:block;font-size:1.35rem;color:var(--brand)}
.cost span{font-size:.8rem;color:var(--muted)}
.tag{display:inline-block;font-size:.75rem;padding:0 8px;border-radius:20px;border:1px solid var(--line);margin-left:4px}
.tag.new{border-color:var(--new);color:var(--new)}
details{grid-column:1/-1;font-size:.85rem;color:var(--muted)}details a{color:var(--brand)}
summary{cursor:pointer}h3{margin:36px 0 12px;font-size:1rem;color:var(--muted)}
@media (max-width:600px){.house{grid-template-columns:80px 1fr}.house img{width:80px;height:64px}
.cost{grid-column:1/-1;text-align:right}}
"""


def render(groups: list[tuple[dict, list[dict], bool, bool]], cfg: dict, stats: dict) -> str:
    def card(best, group, suspicious, is_new):
        tags = []
        if is_new:
            tags.append('<span class="tag new">جدید</span>')
        if best["convertible"]:
            tags.append('<span class="tag">قابل تبدیل</span>')
        if best["agency"]:
            tags.append('<span class="tag">مشاور املاک</span>')
        facts = [best["district"],
                 f"{fa_digits(best['area'])} متر" if best["area"] else None,
                 f"{fa_digits(best['rooms'])} خواب" if best["rooms"] is not None else None,
                 f"ساخت {fa_digits(best['year'])}" if best["year"] else None,
                 {0: "همکف", -1: "زیرهمکف"}.get(best["floor"], f"طبقه {fa_digits(best['floor'])}")
                 if best["floor"] is not None else None]
        others = sorted((l for l in group if l is not best), key=lambda l: l.get("cost") or 10**15)
        more = ""
        if others:
            items = "".join(
                f'<li><a href="{l["url"]}" target="_blank" rel="noopener">{html.escape(l["title"])}</a>'
                f' — ودیعه {money(l["deposit"])}، اجاره {money(l["rent"])}</li>' for l in others)
            more = f"<details><summary>{fa_digits(len(others))} آگهی دیگر از همین خانه</summary><ul>{items}</ul></details>"
        img = f'<img src="{html.escape(best["images"][0])}" alt="" loading="lazy" onerror="this.style.visibility=`hidden`">' if best["images"] else "<img alt=''>"
        cost = "نامشخص" if suspicious else money(best["cost"])
        return (f'<article class="house">{img}<div><h2><a href="{best["url"]}" target="_blank" rel="noopener">'
                f'{html.escape(best["title"])}</a></h2><p class="facts">{html.escape("، ".join(f for f in facts if f))}</p>'
                f'<p class="facts">ودیعه {money(best["deposit"])} | اجاره {money(best["rent"])}</p>{"".join(tags)}</div>'
                f'<div class="cost"><b>{cost}</b><span>هزینه‌ی ماهانه‌ی معادل</span></div>{more}</article>')

    good = [g for g in groups if not g[2]]
    bad = [g for g in groups if g[2]]
    good.sort(key=lambda g: g[0]["cost"])
    rate = fa_digits(f"{cfg['conversion_rate_monthly'] * 100:g}")
    body = "".join(card(*g) for g in good)
    if bad:
        body += "<h3>قیمت توافقی یا غیرواقعی</h3>" + "".join(card(*g) for g in bad)
    if not groups:
        body = "<p>آگهی‌ای با این فیلترها پیدا نشد. فیلترهای آدرس جست‌وجو یا بخش filters در config.json را بازتر کن.</p>"
    sub = (f"{fa_digits(stats['houses'])} خانه از {fa_digits(stats['posts'])} آگهی "
           f"(به‌روزرسانی {fa_digits(datetime.now().strftime('%H:%M'))}). "
           f"هزینه‌ی معادل = اجاره + {rate}٪ ودیعه در ماه.")
    return (f'<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1"><title>خانه‌های اجاره‌ای</title>'
            f'<style>{CSS}</style></head><body><main><h1>خانه‌های اجاره‌ای، ارزان‌ترین اول</h1>'
            f'<p class="sub">{sub}</p>{body}</main></body></html>')


# ------------------------------------------------------------------ تلگرام

def alert_text(reason: str, best: dict, n: int) -> str:
    extra = f"\n({fa_digits(n)} آگهی از همین خانه، ارزان‌ترین:)" if n > 1 else ""
    year = f"\nسال ساخت: {fa_digits(best['year'])}" if best.get("year") else ""
    return (f"<b>{reason}</b>{extra}\n{html.escape(best['title'])}\n{html.escape(best['district'])}"
            f"\nودیعه {money(best['deposit'])} | اجاره {money(best['rent'])}"
            f"\nهزینه‌ی معادل ماهانه: {money(best['cost'])}{year}\n{best['url']}")


def to_jpeg(data: bytes | None) -> bytes | None:
    """عکس‌های دیوار webp هستند؛ تلگرام JPEG را بی‌دردسر به‌عنوان عکس نشان می‌دهد."""
    if not data or Image is None:
        return data
    try:
        im = Image.open(io.BytesIO(data)).convert("RGB")
        im.thumbnail((1280, 1280))
        out = io.BytesIO()
        im.save(out, "JPEG", quality=85)
        return out.getvalue()
    except Exception:
        return None


def telegram(cfg: dict, text: str, photos: list[bytes] = ()):
    """پیام را می‌فرستد؛ اگر عکس باشد به‌صورت آلبوم و متن به‌عنوان توضیح عکس اول."""
    tg = cfg.get("telegram") or {}
    if not tg.get("bot_token") or not tg.get("chat_id"):
        return
    if len(photos) > 1:
        media = [{"type": "photo", "media": f"attach://p{i}"} for i in range(len(photos))]
        media[0].update(caption=text, parse_mode="HTML")
        method, data = "sendMediaGroup", {"media": json.dumps(media)}
        files = {f"p{i}": (f"p{i}.jpg", b) for i, b in enumerate(photos)}
    elif photos:
        method, data, files = "sendPhoto", {"caption": text, "parse_mode": "HTML"}, {"photo": ("p.jpg", photos[0])}
    else:
        method, data, files = "sendMessage", {"text": text, "parse_mode": "HTML", "disable_web_page_preview": "true"}, None
    try:
        for _ in range(2):
            r = requests.post(f"https://api.telegram.org/bot{tg['bot_token']}/{method}", timeout=60,
                              data={"chat_id": tg["chat_id"], **data}, files=files)
            if r.status_code != 429:
                break
            # محدودیت سرعت تلگرام: همان‌قدر که خودش می‌گوید صبر کن و یک بار دیگر بفرست
            time.sleep(((r.json().get("parameters") or {}).get("retry_after") or 5) + 1)
        if not r.ok:  # مثلاً توکن یا chat_id اشتباه
            print(f"  ! تلگرام پیام را نپذیرفت: HTTP {r.status_code} {r.text[:200]}")
            if photos:
                telegram(cfg, text)  # دست‌کم متن اعلان برسد
    except requests.RequestException as e:
        # متن خطا آدرس درخواست را دارد؛ توکن نباید در لاگ بماند
        print(f"  ! ارسال تلگرام ناموفق بود: {str(e).replace(tg['bot_token'], '***')}")
        if photos:
            telegram(cfg, text)


# ------------------------------------------------------------------ اجرای اصلی

def run(cfg: dict):
    dv = Divar(cfg["request_interval_seconds"])
    db = open_db(cfg["db_path"])
    now = time.time()
    # پایه فقط وقتی ثبت‌شده حساب می‌شود که یک اجرا تا آخر رفته باشد (notified پر شده باشد)؛
    # اجرای نیمه‌کاره نباید باعث شود دور بعد همه‌ی خانه‌ها «جدید» اعلان شوند.
    first_run = db.execute("SELECT COUNT(*) FROM notified").fetchone()[0] == 0
    run_id = db.execute("INSERT INTO runs(at) VALUES(?)", (now,)).lastrowid
    refresh = cfg["detail_refresh_hours"] * 3600

    for url in cfg["search_urls"]:
        body, warns = url_to_body(url)
        for w in warns:
            print("  !", w)
        print(f"جست‌وجو: {url}")
        total, cap = dv.count(body), cfg["max_pages"] * 24
        if total is not None:
            note = f"؛ با max_pages={cfg['max_pages']} حداکثر {fa_digits(f'{cap:,}')} تا خوانده می‌شود" if total > cap else ""
            print(f"  حدود {fa_digits(f'{total:,}')} آگهی{note}")
        for row in iter_search(dv, body, cfg["max_pages"]):
            info = row_info(row)
            if not info["token"]:
                continue
            old = db.execute("SELECT data, sig, detail_at FROM posts WHERE token=?", (info["token"],)).fetchone()
            if old and old[1] == info["sig"] and now - (old[2] or 0) < refresh:
                db.execute("UPDATE posts SET last_seen=?, run=? WHERE token=?", (now, run_id, info["token"]))
                continue
            try:
                det = parse_detail(dv.detail(info["token"]))
            except Exception as e:
                print(f"  ! جزئیات {info['token']} گرفته نشد: {e}")
                continue
            listing = build_listing(info, det)
            prev = json.loads(old[0]) if old else None
            if prev and prev.get("images") == listing["images"]:
                listing["img_hashes"] = prev.get("img_hashes", [])
            else:
                for u in listing["images"][: cfg["max_images_per_post"]]:
                    h = dhash(dv.image(u))
                    if h is not None:
                        listing["img_hashes"].append(h)
            db.execute("""INSERT INTO posts(token,data,sig,first_seen,last_seen,detail_at,run)
                          VALUES(?,?,?,?,?,?,?) ON CONFLICT(token) DO UPDATE SET
                          data=excluded.data, sig=excluded.sig, last_seen=excluded.last_seen,
                          detail_at=excluded.detail_at, run=excluded.run""",
                       (info["token"], json.dumps(listing, ensure_ascii=False), info["sig"], now, now, now, run_id))
            print(f"  + {listing['title'][:50]}")
        db.commit()

    rows = db.execute("SELECT data, first_seen FROM posts WHERE run=?", (run_id,)).fetchall()
    listings = []
    for data, first_seen in rows:
        l = json.loads(data)
        l["cost"] = monthly_cost(l, cfg["conversion_rate_monthly"])
        l["is_new"] = first_seen >= now
        if passes_filters(l, cfg):
            listings.append(l)

    groups, alerts = [], []
    for g in cluster(listings):
        best, suspicious = pick_best(g, cfg)
        is_new = all(l["is_new"] for l in g)
        groups.append((best, g, suspicious, is_new))
        if suspicious:
            continue
        tokens = [l["token"] for l in g]
        marks = ",".join("?" * len(tokens))
        prev = db.execute(f"SELECT MIN(best_cost) FROM notified WHERE token IN ({marks})", tokens).fetchone()[0]
        reason = "خانه‌ی جدید" if prev is None else ("قیمت بهتر" if best["cost"] < prev * 0.99 else None)
        if reason:
            alerts.append((reason, best, len(g)))
            db.executemany("INSERT OR REPLACE INTO notified VALUES(?,?,?)", [(t, best["cost"], now) for t in tokens])
    db.commit()

    Path(cfg["report_path"]).write_text(
        render(groups, cfg, {"houses": len(groups), "posts": len(listings)}), encoding="utf-8")
    print(f"\n{len(listings)} آگهی → {len(groups)} خانه. گزارش: {Path(cfg['report_path']).resolve()}")

    if first_run:
        print("اجرای اول بود؛ برای جلوگیری از سیل پیام، اعلان تلگرام از اجرای بعدی فرستاده می‌شود.")
        return
    tg = cfg["telegram"]
    max_photos = min(int(tg.get("max_photos") or 0), 10) if tg.get("bot_token") and tg.get("chat_id") else 0
    for reason, best, n in alerts:
        # آگهی‌هایی که قبل از اضافه شدن photos ذخیره شده‌اند فقط عکس کوچک دارند
        urls = (best.get("photos") or best["images"])[:max_photos]
        photos = [p for p in (to_jpeg(dv.image(u)) for u in urls) if p]
        telegram(cfg, alert_text(reason, best, n), photos)
    print(f"{len(alerts)} اعلان.")


def load_config(path: str) -> dict:
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    # config.local.json (در git نیست) برای توکن و تنظیمات شخصی، روی config.json اعمال می‌شود
    local = Path(path).with_name(Path(path).stem + ".local.json")
    for p in (Path(path), local):
        if not p.exists() and p == local:
            continue
        for k, v in json.loads(p.read_text(encoding="utf-8")).items():
            if isinstance(v, dict) and isinstance(cfg.get(k), dict):
                cfg[k].update(v)
            else:
                cfg[k] = v
    # روی GitHub Actions توکن از Secrets می‌آید
    for key, env in (("bot_token", "TELEGRAM_BOT_TOKEN"), ("chat_id", "TELEGRAM_CHAT_ID")):
        if os.environ.get(env):
            cfg["telegram"][key] = os.environ[env]
    if not cfg["search_urls"]:
        sys.exit("در config.json حداقل یک آدرس در search_urls بگذار.")
    return cfg


def main():
    ap = argparse.ArgumentParser(description="کرال آگهی‌های اجاره دیوار با حذف تکراری‌ها")
    ap.add_argument("--config", default="config.json")
    ap.add_argument("--loop", type=float, default=0, help="هر چند دقیقه یک بار اجرا شود (۰ = یک بار)")
    args = ap.parse_args()
    cfg = load_config(args.config)
    while True:
        try:
            run(cfg)
        except Exception as e:
            print(f"خطا: {e}")
            if not args.loop:
                raise
        if not args.loop:
            break
        time.sleep(args.loop * 60)


if __name__ == "__main__":
    main()
