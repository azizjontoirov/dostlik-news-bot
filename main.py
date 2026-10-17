#!/usr/bin/env python3
"""
DO'STLIK BOZOR | YANGILIKLAR — Telegram yangiliklar boti (v3).

Oqim:
  1. (har kuni soat 06:00 da, bir marta) ob-havo + valyuta posti (rasmsiz).
  2. gov.uz/jizzax va respublika RSS manbalaridan yangi xabarlarni yig'ish.
  3. Maqola sahifasidan rasm (og:image) va to'liq matnni olish.
  4. Groq AI: O'zbekistonga aloqadorligini baholash (aks holda SKIP) + o'zbek lotin imlosida qayta yozish.
  5. Post RASM + CAPTION (1024 belgiga sig'adigan) ko'rinishida kanal(lar)ga joylanadi.

Muhit o'zgaruvchilari:
  TELEGRAM_BOT_TOKEN  (majburiy)
  TELEGRAM_CHAT_ID    (majburiy; bir nechta kanal bo'lsa vergul bilan: "@kanal1,@kanal2")
  GROQ_API_KEY        (ixtiyoriy; bo'lmasa AI'siz zaxira format ishlatiladi)
  GROQ_MODELS         (ixtiyoriy; vergul bilan, birinchisi asosiy model)
  DEFAULT_IMAGE_URL   (ixtiyoriy; yangilikda rasm topilmasa ishlatiladigan umumiy rasm, masalan kanal logotipi)
  REQUIRE_IMAGE       (ixtiyoriy; "0" bo'lsa rasmsiz postlarga ham ruxsat. Standart: "1")
"""
from __future__ import annotations

import calendar
import collections
import html
import json
import logging
import mimetypes
import os
import re
import sys
import tempfile
import time
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from enum import Enum
from pathlib import Path
from typing import Any, Optional
from urllib.parse import urljoin
from zoneinfo import ZoneInfo

import feedparser
import requests
from bs4 import BeautifulSoup
import groq as groq_sdk
from groq import Groq
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ──────────────────────────── SOZLAMALAR ────────────────────────────

LOG = logging.getLogger("newsbot")

# Groq'ga ulanish/timeout xatolari: shunda boshqa modellarni sinash befoyda (tarmoq yo'li bir xil) — darhol to'xtaymiz
_NETWORK_ERRORS = tuple(
    t for t in (getattr(groq_sdk, "APIConnectionError", None), getattr(groq_sdk, "APITimeoutError", None)) if t
)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_IDS = [
    c.strip() for c in os.environ.get("TELEGRAM_CHAT_ID", "").split(",") if c.strip()
]
GROQ_API_KEY = os.environ.get("GROQ_API_KEY", "").strip()
DEFAULT_IMAGE_URL = os.environ.get("DEFAULT_IMAGE_URL", "").strip()
REQUIRE_IMAGE = os.environ.get("REQUIRE_IMAGE", "1").strip() != "0"

# Birinchi model asosiy. O'zbek tilidagi sifat modelga qarab farq qiladi — natijaga qarab
# GROQ_MODELS orqali tartibni kodsiz o'zgartirishingiz mumkin. Limit tugasa/xato bo'lsa keyingisiga o'tiladi.
DEFAULT_GROQ_MODELS = [
    "openai/gpt-oss-120b",
    "llama-3.3-70b-versatile",
    "openai/gpt-oss-20b",
    "llama-3.1-8b-instant",
]
GROQ_MODELS = [
    m.strip() for m in os.environ.get("GROQ_MODELS", "").split(",") if m.strip()
] or DEFAULT_GROQ_MODELS

TZ = ZoneInfo("Asia/Tashkent")  # GitHub Actions UTC'da ishlaydi

RSS_FEEDS = [
    "https://kun.uz/news/rss",
    "https://daryo.uz/rss/",
    "https://qalampir.uz/uz/rss",
    "https://www.gazeta.uz/uz/rss/",
]
GOV_NEWS_URL = "https://gov.uz/uz/jizzax/news"
CBU_RATES_URL = "https://cbu.uz/uz/arkhiv-kursov-valyut/json/"
WEATHER_URL = (
    "https://api.open-meteo.com/v1/forecast?latitude=40.1158&longitude=67.8422"
    "&daily=temperature_2m_max,temperature_2m_min,precipitation_sum&timezone=Asia%2FTashkent"
)

SEEN_FILE = "seen_news.json"
DAILY_STATE_FILE = "daily_state.json"
SEEN_LIMIT = 1500

MAX_POSTS_PER_RUN = 1          # bir ishga tushishda ko'pi bilan nechta post
MAX_EVALUATE_PER_RUN = 15      # bir ishga tushishda ko'pi bilan nechta yangilik ko'rib chiqiladi (AI limiti uchun)
ENTRIES_PER_FEED = 10
MAX_AGE_HOURS = 24             # bundan eski RSS yozuvlari e'tiborga olinmaydi
MAX_TELEGRAM_FAILURES = 2
MORNING_HOUR = 6               # ertalabki ob-havo/valyuta posti shu soatda chiqadi (Toshkent vaqti)
MORNING_WINDOW_MIN = 30        # 06:00–06:29 oralig'idagi birinchi ishga tushishda; 06:30 dan keyin KECH chiqmaydi
RUN_BUDGET_SEC = 360           # bir ishga tushishning "yumshoq" vaqt chegarasi (workflow timeout = 10 daqiqa)
AI_BUDGET_SEC = 120            # bir ishga tushishda Groq'ka sarflanadigan umumiy vaqt; oshsa AI o'chiriladi
POST_DELAY_SEC = 2
ADS_FILE = "ads.json"
POSTS_PER_AD = 4               # reklama chiqishi uchun kamida shuncha yangilik posti bo'lishi kerak
MIN_AD_INTERVAL_MIN = 120      # ikki reklama orasidagi minimal vaqt (daqiqa) — kuniga ~7 tadan oshmasligi uchun
AD_HOURS = range(8, 22)        # reklama faqat 08:00–21:59 (Toshkent) oralig'ida chiqadi; kechasi o'quvchi yo'q
PAID_SLOTS_PER_PERMANENT = 1   # har 1 ta pullik reklamadan keyin 1 ta doimiy reklama (1 = navbatma-navbat; 2 = pulliklarga ko'proq)
AD_DELAY_SEC = 3               # yangilik posti bilan reklama orasidagi pauza
MIN_POST_INTERVAL_MIN = 10     # oxirgi postdan beri shuncha daqiqa o'tmagan bo'lsa, yangi post joylanmaydi (ketma-ket/kechikkan ishga tushishlardan himoya). Cron oralig'idan KICHIK bo'lishi shart

CAPTION_LIMIT = 1024
CAPTION_SAFETY = 30            # emoji/entity hisobidagi farqlar uchun zaxira
MESSAGE_LIMIT = 4096
MIN_DETAIL_CHARS = 200         # RSS matni shundan qisqa bo'lsa, maqola sahifasidan to'ldiriladi
MAX_IMAGE_BYTES = 9_000_000
GROQ_TIMEOUT = 20.0

BROWSER_UA = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0 Safari/537.36"
)

FOOTER_HTML = (
    "\n\n\n"
    "🛒 <b>Bizning kanallar:</b>\n"
    "📢 @dostlik_bozor2 | @Dostlik_jizzax1\n\n"
    "👨‍💻 <b>Reklama joylash uchun:</b>\n"
    "👉 @shohrux_1308\n"
    "👉 @azizjon_dev"
)

# AI ishlamagan holatda (zaxira rejim) O'zbekistonga aloqadorlikni taxminan aniqlash uchun (lotin + kirill)
_LOCAL_KEYWORDS = re.compile(
    r"o['ʻʼ’‘`]?zbek|toshkent|jizzax|do['ʻʼ’‘`]?stlik|samarqand|buxoro|farg['ʻʼ’‘`]?ona|andijon|namangan|"
    r"qashqadaryo|surxondaryo|xorazm|navoiy|sirdaryo|qoraqalpo|prezident|mirziyoyev|hokim|vazirlar mahkamasi|"
    r"so['ʻʼ’‘`]?m\b|ўзбек|узбек|тошкент|ташкент|жиззах|джизак|дўстлик|самарқанд|самарканд|бухоро|фарғона|"
    r"андижон|наманган|қашқадарё|сурхондарё|хоразм|навоий|сирдарё|қорақалпоқ|президент|мирзиёев|мирзиёев|ҳоким|сўм\b",
    re.IGNORECASE,
)

SKIP = "__SKIP__"            # AI: "bu yangilik kanalga mos emas"
DUPLICATE = "__DUPLICATE__"  # AI: "bu voqea kanalda allaqachon joylangan"

# Boshqa saytdagi takrorlarni aniqlash (recent_posts)
RECENT_MAX_ITEMS = 40          # eslab qolinadigan oxirgi postlar soni
RECENT_MAX_AGE_HOURS = 72      # shuncha soatdan eskilari unutiladi
RECENT_IN_PROMPT = 15          # AI'ga ko'rsatiladigan oxirgi sarlavhalar soni
DUP_MIN_SHARED = 4             # kod bilan "aniq takror" deyish uchun kamida shuncha umumiy so'z
DUP_JACCARD = 0.7              # ...va o'xshashlik darajasi (chegaradagi holatlarni AI hal qiladi)


# ──────────────────────────── YORDAMCHI FUNKSIYALAR ────────────────────────────


def build_session() -> requests.Session:
    """Retry va backoff'li HTTP sessiya (faqat GET; POST takrorlanishi Telegram'da qo'lda boshqariladi)."""
    retry = Retry(
        total=3, connect=3, read=3, backoff_factor=1.5,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset(["GET"]),
        respect_retry_after_header=True,
    )
    adapter = HTTPAdapter(max_retries=retry)
    session = requests.Session()
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    session.headers.update({"User-Agent": BROWSER_UA, "Accept-Language": "uz,ru;q=0.8,en;q=0.5"})
    return session


def load_json(path: str, default: Any) -> Any:
    """JSON'ni xavfsiz o'qish: fayl yo'q/buzilgan bo'lsa default qaytaradi (buzilgan fayl .corrupt'ga ko'chiriladi)."""
    p = Path(path)
    if not p.exists():
        return default
    try:
        with p.open("r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        LOG.warning("%s o'qilmadi (%s). Yangi fayl bilan davom etiladi.", path, exc)
        try:
            p.replace(p.with_name(p.name + ".corrupt"))
        except OSError:
            pass
        return default
    if not isinstance(data, type(default)):
        LOG.warning("%s kutilgan formatda emas — e'tiborsiz qoldirildi.", path)
        return default
    return data


def save_json(path: str, data: Any) -> bool:
    """Atomik yozish: vaqtinchalik faylga yozib, so'ng os.replace."""
    p = Path(path)
    tmp_name: Optional[str] = None
    try:
        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", dir=p.parent if str(p.parent) else ".", delete=False, suffix=".tmp"
        ) as tmp:
            tmp_name = tmp.name
            json.dump(data, tmp, ensure_ascii=False, indent=2)
            tmp.flush()
            os.fsync(tmp.fileno())
        os.replace(tmp_name, p)
        return True
    except OSError as exc:
        LOG.error("%s saqlanmadi: %s", path, exc)
        if tmp_name:
            try:
                os.unlink(tmp_name)
            except OSError:
                pass
        return False


def clean_html(text: str, limit: int = 1500) -> str:
    if not text:
        return ""
    plain = BeautifulSoup(text, "html.parser").get_text(" ", strip=True)
    return re.sub(r"\s+", " ", plain)[:limit]


def strip_tags(text: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", text))


def shorten(text: str, limit: int) -> str:
    """Matnni imkon qadar gap oxirida qisqartirish."""
    text = text.strip()
    if len(text) <= limit:
        return text
    cut = text[:limit]
    ends = [m.end() for m in re.finditer(r"[.!?…](?=\s|$)", cut)]
    if ends and ends[-1] > limit * 0.5:
        return cut[: ends[-1]].rstrip()
    return cut.rsplit(" ", 1)[0].rstrip(",;:- ") + "…"


_SOURCE_NAMES = re.compile(
    r"(?:\b(?:manba|source|via)\s*[:\-–]\s*)?#?\b(?:kun|daryo|qalampir|gazeta|gov)\.?\s?uz\b", re.IGNORECASE
)
_SOURCE_LINE = re.compile(r"^\s*(?:manba|источник|source|via)\s*[:\-–].*$", re.IGNORECASE | re.MULTILINE)


def scrub_sources(text: str) -> str:
    """AI e'tiborsizlik qilib manba nomini yozib yuborsa ham, uni olib tashlaydi."""
    text = _SOURCE_LINE.sub("", text)
    text = _SOURCE_NAMES.sub("", text)
    return re.sub(r"[ \t]{2,}", " ", text)


def normalize_apostrophes(text: str) -> str:
    """oʻ / gʻ / ’ / ‘ / ` kabi turli apostroflarni bitta (') ga keltiradi — imlo bir xil chiqadi."""
    return re.sub(r"[ʻʼʹ‘’`´′]", "'", text)


_BOLD = re.compile(r"\*\*(.+?)\*\*")


def to_telegram_html(text: str) -> str:
    """Matnni Telegram HTML'ga xavfsiz aylantiradi (`**qalin**` → <b>, qolgan belgilar escape qilinadi)."""
    text = text.replace("\r\n", "\n")
    text = re.sub(r"^\s{0,3}#{1,6}\s+", "", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*[*\-]\s+", "• ", text, flags=re.MULTILINE)
    text = html.escape(text, quote=False)
    text = _BOLD.sub(r"<b>\1</b>", text)
    text = text.replace("*", "")
    text = re.sub(r"\n{4,}", "\n\n\n", text)
    return text.strip()


def caption_budget() -> int:
    """Footer'dan keyin post matni uchun qolgan belgilar soni (rasm caption'i 1024 belgi bilan cheklangan)."""
    return CAPTION_LIMIT - len(strip_tags(FOOTER_HTML)) - CAPTION_SAFETY


def fit_caption(body: str, budget: int) -> str:
    """Matn caption'ga sig'maydigan bo'lsa, xeshteglarni saqlagan holda gap oxirida qisqartiradi."""
    body = body.strip()

    def plain_len(t: str) -> int:
        return len(strip_tags(to_telegram_html(t)))

    if plain_len(body) <= budget:
        return body

    lines = body.split("\n")
    tags = ""
    if lines and re.fullmatch(r"(?:#\S+\s*)+", lines[-1].strip()):
        tags = lines.pop().strip()
    main = "\n".join(lines).strip()

    allowed = budget - (len(tags) + 2 if tags else 0)
    result = body
    for _ in range(8):
        candidate = shorten(main, allowed)
        result = f"{candidate}\n\n{tags}" if tags else candidate
        if plain_len(result) <= budget:
            return result
        allowed -= 40
    return result


def looks_local(item: "NewsItem") -> bool:
    """Zaxira rejim uchun taxminiy tekshiruv: yangilik O'zbekistonga aloqadorga o'xshaydimi."""
    return bool(_LOCAL_KEYWORDS.search(f"{item.title} {item.summary}"))


def get_json(session: requests.Session, url: str) -> Any:
    res = session.get(url, timeout=15)
    res.raise_for_status()
    return res.json()


# ──────────────────────────── HOLAT SAQLASH ────────────────────────────


class SeenStore:
    """Ko'rilgan yangiliklar to'plami (tartibni saqlaydi, hajmi cheklangan)."""

    def __init__(self, path: str, limit: int = SEEN_LIMIT) -> None:
        self.path = path
        self.limit = limit
        raw = load_json(path, [])
        self._items: list[str] = list(dict.fromkeys(str(x) for x in raw if x))
        self._set = set(self._items)

    def seen(self, keys: list[str]) -> bool:
        return any(k in self._set for k in keys)

    def add(self, keys: list[str]) -> None:
        for k in keys:
            if k and k not in self._set:
                self._set.add(k)
                self._items.append(k)

    def save(self) -> bool:
        self._items = self._items[-self.limit:]
        self._set = set(self._items)
        return save_json(self.path, self._items)


_CYR2LAT = {
    "а": "a", "б": "b", "в": "v", "г": "g", "д": "d", "е": "e", "ё": "yo", "ж": "j", "з": "z", "и": "i",
    "й": "y", "к": "k", "л": "l", "м": "m", "н": "n", "о": "o", "п": "p", "р": "r", "с": "s", "т": "t",
    "у": "u", "ф": "f", "х": "x", "ц": "ts", "ч": "ch", "ш": "sh", "щ": "sh", "ъ": "", "ы": "i", "ь": "",
    "э": "e", "ю": "yu", "я": "ya", "ў": "o", "қ": "q", "ғ": "g", "ҳ": "h",
}


def title_stems(text: str) -> set[str]:
    """Sarlavhani taqqoslash uchun: kirill -> lotin, apostrofsiz, so'zlarning dastlabki 5 harfi (qo'shimchalarga bardosh)."""
    latin = "".join(_CYR2LAT.get(ch, ch) for ch in text.lower())
    latin = re.sub(r"['ʻʼʹ‘’`´′]", "", latin)
    words = re.findall(r"[a-z0-9]+", latin)
    return {w[:5] for w in words if len(w) >= 4 or (w.isdigit() and len(w) >= 2)}


def is_similar_title(a: str, b: str) -> bool:
    sa, sb = title_stems(a), title_stems(b)
    shared = len(sa & sb)
    if shared < DUP_MIN_SHARED:
        return False
    return shared / len(sa | sb) >= DUP_JACCARD


def extract_headline(body: str) -> str:
    """Post matnining birinchi qatori (emoji va ** belgilarisiz)."""
    for line in body.splitlines():
        line = re.sub(r"[*_]", "", line.strip())
        line = re.sub(r"^[^\w]+", "", line)
        if line:
            return line[:150]
    return ""


class RecentPosts:
    """
    Oxirgi joylangan postlar xotirasi (daily_state.json ichida). Maqsad: bir voqea turli saytlarda
    (Kun.uz, Gazeta.uz, Daryo.uz...) chiqqanda ikkinchi marta joylanmasligi.
    """

    def __init__(self, state: dict[str, Any]) -> None:
        self.state = state
        cutoff = time.time() - RECENT_MAX_AGE_HOURS * 3600
        raw = state.get("recent_posts")
        raw = raw if isinstance(raw, list) else []
        self.items: list[dict[str, Any]] = [
            e for e in raw if isinstance(e, dict) and float(e.get("ts", 0)) >= cutoff
        ]
        state["recent_posts"] = self.items

    def headlines(self, n: int = RECENT_IN_PROMPT) -> list[str]:
        return [e["headline"] for e in self.items[-n:] if e.get("headline")]

    def is_duplicate(self, title: str) -> bool:
        return any(
            is_similar_title(title, e.get("source_title", "")) or is_similar_title(title, e.get("headline", ""))
            for e in self.items
        )

    def add(self, source_title: str, headline: str) -> None:
        self.items.append({"source_title": source_title, "headline": headline, "ts": time.time()})
        self.items = self.items[-RECENT_MAX_ITEMS:]
        self.state["recent_posts"] = self.items
        save_json(DAILY_STATE_FILE, self.state)


# ──────────────────────────── MA'LUMOT MANBALARI ────────────────────────────


@dataclass
class NewsItem:
    uid: str
    title: str
    summary: str
    link: str = ""
    image_url: Optional[str] = None
    published_ts: float = 0.0  # e'lon qilingan vaqt (unix); navbatni aniqlash uchun
    headline: str = ""         # kanalga joylangan post sarlavhasi (takrorlarni aniqlash uchun)
    note: str = ""             # qaror sababi (log statistikasi uchun)

    @property
    def dedup_keys(self) -> list[str]:
        title_key = re.sub(r"\W+", "", self.title.lower())[:30]
        return [k for k in (self.uid, title_key) if k]


def extract_image_url(entry: Any) -> Optional[str]:
    candidates: list[Optional[str]] = []
    for attr in ("media_content", "media_thumbnail"):
        for m in entry.get(attr) or []:
            candidates.append(m.get("url"))
    for enc in entry.get("enclosures") or []:
        if str(enc.get("type", "")).startswith("image/"):
            candidates.append(enc.get("href") or enc.get("url"))
    html_blobs = [entry.get("summary", "")] + [c.get("value", "") for c in entry.get("content") or []]
    for blob in html_blobs:
        if blob:
            img = BeautifulSoup(blob, "html.parser").find("img")
            if img and img.get("src"):
                candidates.append(img["src"])
    for url in candidates:
        if url and url.startswith(("http://", "https://")):
            return url
    return None


def fetch_rss_items(session: requests.Session, feed_url: str) -> list[NewsItem]:
    LOG.info("Manba tekshirilmoqda: %s", feed_url)
    try:
        res = session.get(feed_url, timeout=15)
        res.raise_for_status()
    except requests.RequestException as exc:
        LOG.warning("RSS yuklanmadi (%s): %s", feed_url, exc)
        return []

    feed = feedparser.parse(res.content)
    if not feed.entries:
        LOG.warning("RSS'da yozuv topilmadi yoki format buzuq: %s", feed_url)
        return []

    items: list[NewsItem] = []
    now_ts = time.time()
    for position, entry in enumerate(feed.entries[:ENTRIES_PER_FEED]):
        title = (entry.get("title") or "").strip()
        link = entry.get("link") or ""
        uid = entry.get("id") or link
        if not title or not uid:
            continue
        published = entry.get("published_parsed") or entry.get("updated_parsed")
        published_ts = calendar.timegm(published) if published else now_ts - position * 60
        if now_ts - published_ts > MAX_AGE_HOURS * 3600:
            continue  # eski yangilik
        summary = clean_html(entry.get("summary") or entry.get("description") or "")
        items.append(NewsItem(uid=uid, title=title, summary=summary, link=link,
                              image_url=extract_image_url(entry), published_ts=published_ts))
    return items


def _find_og_image(soup: BeautifulSoup, base_url: str) -> Optional[str]:
    for attrs in ({"property": "og:image"}, {"name": "twitter:image"}, {"property": "og:image:url"}):
        tag = soup.find("meta", attrs=attrs)
        if tag and tag.get("content"):
            url = urljoin(base_url, tag["content"].strip())
            if url.startswith(("http://", "https://")):
                return url
    return None


def _extract_article_text(soup: BeautifulSoup) -> str:
    container = soup.find("article") or soup
    paragraphs = [p.get_text(" ", strip=True) for p in container.find_all("p")]
    body = " ".join(p for p in paragraphs if len(p) > 40)
    if body:
        return re.sub(r"\s+", " ", body)[:1500]
    meta = soup.find("meta", attrs={"property": "og:description"})
    return clean_html(meta["content"]) if meta and meta.get("content") else ""


def enrich_item(session: requests.Session, item: NewsItem) -> None:
    """Rasm yo'q yoki matn qisqa bo'lsa — maqola sahifasidan og:image va to'liq matnni oladi (bitta so'rov)."""
    need_image = not item.image_url
    need_text = len(item.summary) < MIN_DETAIL_CHARS
    if not item.link or not (need_image or need_text):
        return
    try:
        res = session.get(item.link, timeout=15)
        res.raise_for_status()
    except requests.RequestException as exc:
        LOG.warning("Maqola sahifasi ochilmadi (%s): %s", item.link, exc)
        return
    soup = BeautifulSoup(res.content, "html.parser")
    if need_image:
        item.image_url = _find_og_image(soup, item.link)
    if need_text:
        text = _extract_article_text(soup)
        if len(text) > len(item.summary):
            item.summary = text


def fetch_gov_item(session: requests.Session) -> Optional[NewsItem]:
    """gov.uz/jizzax bo'limidagi eng so'nggi yangilik (matn va rasm keyinroq enrich_item orqali olinadi)."""
    try:
        res = session.get(GOV_NEWS_URL, timeout=15)
        res.raise_for_status()
    except requests.RequestException as exc:
        LOG.warning("gov.uz/jizzax yuklanmadi: %s", exc)
        return None

    soup = BeautifulSoup(res.content, "html.parser")
    for a in soup.find_all("a", href=re.compile(r"/jizzax/news/[^/?#]+")):
        title = a.get_text(" ", strip=True)
        if len(title) < 15:
            continue
        link = urljoin("https://gov.uz", a["href"])
        # Viloyat hokimligi xabari kanal uchun eng dolzarb — navbatda birinchi turishi uchun "hozirgi" vaqt beriladi
        return NewsItem(uid=link, title=title, summary="", link=link, published_ts=time.time())

    LOG.warning("gov.uz/jizzax'da maqola havolasi topilmadi (sayt tuzilishi o'zgargan bo'lishi mumkin).")
    return None


def iter_candidates(session: requests.Session) -> list[NewsItem]:
    """Barcha manbalardan yig'ib, eng yangisidan boshlab tartiblaydi (bitta sayt navbatni egallab olmasligi uchun)."""
    items: list[NewsItem] = []
    try:
        gov = fetch_gov_item(session)
        if gov:
            items.append(gov)
    except Exception:  # noqa: BLE001 — bitta manba butun ishni to'xtatib qo'ymasin
        LOG.exception("gov.uz manbasida kutilmagan xatolik")
    for feed_url in RSS_FEEDS:
        try:
            got = fetch_rss_items(session, feed_url)
        except Exception:  # noqa: BLE001
            LOG.exception("RSS qayta ishlashda kutilmagan xatolik: %s", feed_url)
            got = []
        LOG.info("  → %s: %d ta yangi (24 soat ichida) yozuv", feed_url, len(got))
        items.extend(got)
    items.sort(key=lambda it: it.published_ts, reverse=True)
    LOG.info("Jami nomzod yangilik: %d ta", len(items))
    return items


# ──────────────────────────── AI (GROQ) ────────────────────────────

SYSTEM_PROMPT = (
    "Siz 'DO'STLIK BOZOR | YANGILIKLAR' Telegram kanalining tajribali jurnalisti va muharririsiz. "
    "Kanal Jizzax viloyati va Do'stlik tumani aholisiga, umuman O'zbekiston fuqarolariga mo'ljallangan. "
    "Siz o'zbek tilini (lotin alifbosi) mukammal bilasiz va imlo hamda grammatik xatolarga yo'l qo'ymaysiz."
)

USER_PROMPT = """Quyidagi yangilikni baholang va Telegram uchun post tayyorlang.

{recent_block}1-QADAM — MOSLIGINI TEKSHIRING.
Kanal asosan O'zbekiston hayotiga oid yangiliklarni joylaydi: O'zbekiston va uning viloyatlari, hukumat qarorlari,
iqtisodiyot, narxlar, valyuta, ta'lim, sog'liq, transport, qurilish, qishloq xo'jaligi, ob-havo, hodisalar, madaniyat,
sport (O'zbekiston sportchilari/jamoalari), shuningdek O'zbekiston fuqarolariga bevosita ta'sir qiladigan xorijiy yangiliklar
(mehnat migratsiyasi, vizalar, yaqin davlatlar bilan hamkorlik va h.k.).
Quyidagilar MOS EMAS: O'zbekistonga aloqasi yo'q xorijiy mashhurlar, avtomobil/gadjet/texnologiya yangiliklari,
xorijdagi jinoyat va voqealar, reklama xarakteridagi materiallar.
Agar yangilik mos bo'lmasa, javobda faqat bitta so'z yozing: SKIP

2-QADAM — AGAR MOS BO'LSA, POST YOZING. Qoidalar:
1. Hech qanday manba nomini (Kun.uz, Daryo.uz, Gazeta.uz, Qalampir.uz, Gov.uz va h.k.) yozmang.
2. Matn qaysi tilda yoki alifboda berilgan bo'lishidan qat'i nazar, post o'zbek tilida, LOTIN alifbosida bo'lsin.
3. Imlo: oʻ va gʻ harflari uchun oddiy apostrof (') ishlating: o'zbek, g'oya, Do'stlik, ma'lumot. Qo'shimchalarni (-ning, -ni, -ga, -da, -dan, -lar) to'g'ri qo'llang. Gaplar sodda, ravon va grammatik to'g'ri bo'lsin. Yozib bo'lgach, matnni imlo va grammatika bo'yicha ichingizda tekshirib chiqing.
4. Rus va ingliz so'zlarining o'zbekcha muqobili bo'lsa, o'zbekchasini ishlating. Ism, lavozim va tashkilot nomlarini aniq yozing.
5. Faqat berilgan faktlardan foydalaning. Raqam, ism, sana va joy nomlarini o'zgartirmang, yangi fakt o'ylab topmang.
6. Tuzilishi: diqqatni tortuvchi sarlavha (1-2 emoji bilan, **qalin**), 1-3 qisqa abzas (abzaslar orasida bo'sh qator), oxirida 2-3 ta xeshteg (masalan: #Jizzax #Dostlik #Yangiliklar).
7. Hajmi: xeshteglar bilan jami {max_chars} belgidan OSHMASIN.
8. Markdown sarlavhalari (#), havolalar va kod bloklaridan foydalanmang.
9. FAQAT tayyor post matnini (yoki SKIP) qaytaring — izoh yoki kirish so'zlarisiz.

Yangilik sarlavhasi: {title}
Yangilik matni: {summary}
"""


class AIRewriter:
    """Groq orqali baholash va qayta yozish: modellar zanjiri, timeout, circuit-breaker."""

    MAX_FAILED_ROUNDS = 2

    def __init__(self, api_key: str, models: list[str]) -> None:
        self.models = models
        self.client: Optional[Groq] = None
        self.failed_rounds = 0
        self.spent_sec = 0.0
        if api_key:
            try:
                self.client = Groq(api_key=api_key, timeout=GROQ_TIMEOUT, max_retries=1)
            except Exception as exc:  # noqa: BLE001
                LOG.error("Groq klienti yaratilmadi: %s", exc)
        else:
            LOG.warning("GROQ_API_KEY topilmadi — AI'siz zaxira format ishlatiladi.")

    @property
    def available(self) -> bool:
        if self.spent_sec >= AI_BUDGET_SEC and self.client is not None:
            LOG.warning("Groq'ga ajratilgan vaqt (%d s) tugadi — bu ishga tushishda AI'siz davom etiladi.", AI_BUDGET_SEC)
            return False
        return self.client is not None and self.failed_rounds < self.MAX_FAILED_ROUNDS

    @staticmethod
    def _sanitize(text: str) -> Optional[str]:
        text = re.sub(r"^```[a-zA-Z]*\n?|```$", "", (text or "").strip(), flags=re.MULTILINE).strip()
        if re.match(r"^\W*SKIP\b", text, re.IGNORECASE) and len(text) < 40:
            return SKIP
        if re.match(r"^\W*DUPLICATE\b", text, re.IGNORECASE) and len(text) < 40:
            return DUPLICATE
        text = normalize_apostrophes(scrub_sources(text)).strip()
        if len(text) < 40 or len(text) > 3000:
            return None
        return text

    def rewrite(self, item: NewsItem, recent_headlines: Optional[list[str]] = None) -> Optional[str]:
        """Post matni, SKIP (mos emas), DUPLICATE (takror) yoki None (AI ishlamadi) qaytaradi."""
        if not self.available:
            return None
        summary = item.summary or "(matn mavjud emas — faqat sarlavhadan foydalaning, yangi faktlar qo'shmang)"
        recent_block = ""
        if recent_headlines:
            listing = "\n".join(f"- {h}" for h in recent_headlines)
            recent_block = (
                "0-QADAM — TAKRORNI TEKSHIRING.\n"
                f"Kanalda yaqinda joylangan yangiliklar:\n{listing}\n"
                "Agar quyidagi yangilik ularning birining AYNAN O'ZI bo'lsa (boshqa sayt, boshqa so'zlar yoki boshqa "
                "alifboda yozilgan bo'lsa ham — bir xil voqea), javobda faqat bitta so'z yozing: DUPLICATE\n"
                "Yangi voqea yoki muhim yangi tafsilot bo'lsa, bu takror emas.\n\n"
            )
        prompt = USER_PROMPT.format(
            title=item.title, summary=summary, max_chars=int(caption_budget() * 0.92),
            recent_block=recent_block,
        )

        started = time.monotonic()
        try:
            for model in self.models:
                try:
                    extra = {"reasoning_effort": "low"} if "gpt-oss" in model else None
                    resp = self.client.chat.completions.create(  # type: ignore[union-attr]
                        model=model,
                        messages=[
                            {"role": "system", "content": SYSTEM_PROMPT},
                            {"role": "user", "content": prompt},
                        ],
                        temperature=0.3,
                        max_tokens=2500,
                        extra_body=extra,
                    )
                    text = self._sanitize(resp.choices[0].message.content)
                    if text:
                        self.failed_rounds = 0
                        label = {SKIP: " — SKIP", DUPLICATE: " — DUPLICATE"}.get(text, "")
                        LOG.info("AI javobi tayyor (model: %s)%s", model, label)
                        return text
                    LOG.warning("Model %s yaroqsiz (bo'sh/juda qisqa/juda uzun) javob qaytardi.", model)
                except Exception as exc:  # noqa: BLE001 — Groq SDK turli xatolik sinflarini beradi
                    LOG.warning("Groq model %s xatoligi [%s]: %s", model, type(exc).__name__, exc)
                    if _NETWORK_ERRORS and isinstance(exc, _NETWORK_ERRORS):
                        LOG.warning("Groq'ga ulanib bo'lmayapti — boshqa modellar sinab ko'rilmaydi.")
                        break
                    time.sleep(1.5)
        finally:
            self.spent_sec += time.monotonic() - started

        self.failed_rounds += 1
        LOG.error("Barcha Groq modellari ishlamadi (%d/%d).", self.failed_rounds, self.MAX_FAILED_ROUNDS)
        return None


def fallback_post_text(item: NewsItem) -> str:
    """AI ishlamaganda ham post toza formatda chiqishi uchun zaxira matn."""
    parts = [f"⚡️ **{scrub_sources(item.title).strip()}**"]
    summary = scrub_sources(shorten(item.summary, 700)).strip()
    if summary:
        parts.append(summary)
    parts.append("#Jizzax #Dostlik #Yangiliklar")
    return "\n\n".join(parts)


def build_final_post(item: NewsItem, ai_text: Optional[str]) -> str:
    body = normalize_apostrophes(ai_text if ai_text else fallback_post_text(item))
    body = fit_caption(body, caption_budget())
    return to_telegram_html(body) + FOOTER_HTML


# ──────────────────────────── TELEGRAM ────────────────────────────

_ERROR_HINTS = (
    ("chat not found", "chat_id noto'g'ri yoki bot kanalga qo'shilmagan (kanalda ADMIN bo'lishi shart)."),
    ("bot was kicked", "Bot kanaldan chiqarib yuborilgan."),
    ("not enough rights", "Botda kanalga post yuborish huquqi yo'q (admin huquqlarini tekshiring)."),
    ("unauthorized", "TELEGRAM_BOT_TOKEN noto'g'ri yoki bekor qilingan."),
    ("can't parse entities", "Formatlash xatosi — matn oddiy ko'rinishda qayta yuboriladi."),
    ("wrong file identifier", "Rasm URL'i yaroqsiz — rasm yuklab olinib, fayl sifatida yuboriladi."),
    ("failed to get http url content", "Telegram rasmni yuklab ola olmadi — rasm fayl sifatida yuboriladi."),
    ("message is too long", "Matn 4096 belgidan uzun."),
)

_IMAGE_ERRORS = (
    "wrong file identifier", "failed to get http url content", "wrong type of the web page content",
    "image_process_failed", "photo_invalid_dimensions", "photo_ext_invalid", "wrong remote file",
    "file is too big", "photo_save_file_invalid", "wrong file",
)


class SendResult(Enum):
    OK = "ok"
    PHOTO_FAILED = "photo_failed"   # muammo rasmning o'zida (post rasmsiz yuborilmaydi)
    FAILED = "failed"               # chat/token/tarmoq muammosi


class TelegramPublisher:
    def __init__(self, token: str, chat_ids: list[str], session: requests.Session) -> None:
        self.token = token
        self.chat_ids = chat_ids
        self.session = session

    def _redact(self, text: str) -> str:
        return text.replace(self.token, "***") if self.token else text

    def _call(self, method: str, payload: dict[str, Any], files: Optional[dict[str, Any]] = None,
              attempts: int = 3) -> tuple[bool, dict[str, Any]]:
        url = f"https://api.telegram.org/bot{self.token}/{method}"
        data: dict[str, Any] = {}
        for attempt in range(1, attempts + 1):
            try:
                res = self.session.post(url, data=payload, files=files, timeout=60 if files else 20)
            except requests.RequestException as exc:
                LOG.warning("Telegram %s tarmoq xatosi (urinish %d/%d): %s",
                            method, attempt, attempts, self._redact(str(exc)))
                time.sleep(2 * attempt)
                continue

            try:
                data = res.json()
            except ValueError:
                data = {"ok": False, "error_code": res.status_code, "description": res.text[:300]}

            if data.get("ok"):
                return True, data

            code = int(data.get("error_code", res.status_code))
            desc = str(data.get("description", "noma'lum xato"))

            if code == 429:
                wait = int(data.get("parameters", {}).get("retry_after", 5))
                if wait <= 60 and attempt < attempts:
                    LOG.warning("Telegram flood limit: %d soniya kutiladi.", wait)
                    time.sleep(wait + 1)
                    continue
            elif code >= 500 and attempt < attempts:
                LOG.warning("Telegram server xatosi %d: %s (qayta uriniladi)", code, desc)
                time.sleep(2 * attempt)
                continue

            hint = next((h for key, h in _ERROR_HINTS if key in desc.lower()), "")
            LOG.error("Telegram API xatosi | method=%s | kod=%s | %s%s",
                      method, code, desc, f" | MASLAHAT: {hint}" if hint else "")
            return False, data

        return False, data

    @staticmethod
    def _is_parse_error(data: dict[str, Any]) -> bool:
        return "can't parse entities" in str(data.get("description", "")).lower()

    @staticmethod
    def _is_image_error(data: dict[str, Any]) -> bool:
        desc = str(data.get("description", "")).lower()
        return any(key in desc for key in _IMAGE_ERRORS)

    def _download_image(self, url: str) -> Optional[bytes]:
        """Telegram URL'dan rasmni ola olmasa (sayt Telegram'ni bloklasa), o'zimiz yuklab, fayl sifatida yuboramiz."""
        try:
            res = self.session.get(url, timeout=20, headers={"Referer": url})
            res.raise_for_status()
        except requests.RequestException as exc:
            LOG.warning("Rasm yuklab olinmadi (%s): %s", url, exc)
            return None
        ctype = res.headers.get("Content-Type", "").lower()
        if not ctype.startswith("image/") or "svg" in ctype:
            LOG.warning("Rasm emas yoki qo'llab-quvvatlanmaydi (%s): %s", ctype, url)
            return None
        if len(res.content) > MAX_IMAGE_BYTES:
            LOG.warning("Rasm juda katta (%d bayt): %s", len(res.content), url)
            return None
        return res.content

    # -- yuborish bosqichlari ---------------------------------------------------
    def _send_text(self, chat_id: str, html_text: str) -> bool:
        payload = {"chat_id": chat_id, "text": html_text, "parse_mode": "HTML", "disable_web_page_preview": "true"}
        ok, data = self._call("sendMessage", payload)
        if not ok and self._is_parse_error(data):
            plain = strip_tags(html_text)[:MESSAGE_LIMIT]
            ok, _ = self._call("sendMessage", {"chat_id": chat_id, "text": plain, "disable_web_page_preview": "true"})
        return ok

    def _photo_call(self, chat_id: str, image_url: Optional[str], files: Optional[dict[str, Any]],
                    caption_html: Optional[str]) -> tuple[bool, dict[str, Any]]:
        payload: dict[str, Any] = {"chat_id": chat_id}
        if image_url:
            payload["photo"] = image_url
        if caption_html:
            payload.update(caption=caption_html, parse_mode="HTML")
        ok, data = self._call("sendPhoto", payload, files=files)
        if not ok and caption_html and self._is_parse_error(data):
            payload.pop("parse_mode", None)
            payload["caption"] = strip_tags(caption_html)[:CAPTION_LIMIT]
            ok, data = self._call("sendPhoto", payload, files=files)
        return ok, data

    def _send_photo(self, chat_id: str, image_url: Optional[str], caption_html: Optional[str],
                    local_image: Optional[tuple[str, bytes, str]] = None) -> SendResult:
        if local_image is not None:  # repo ichidagi fayl: havola ham, public repo ham kerak emas
            ok, data = self._photo_call(chat_id, None, {"photo": local_image}, caption_html)
            if ok:
                return SendResult.OK
            return SendResult.PHOTO_FAILED if self._is_image_error(data) else SendResult.FAILED

        ok, data = self._photo_call(chat_id, image_url, None, caption_html)
        if ok:
            return SendResult.OK
        if not self._is_image_error(data):
            return SendResult.FAILED

        blob = self._download_image(image_url)
        if blob:
            ok, data = self._photo_call(chat_id, None, {"photo": ("photo.jpg", blob)}, caption_html)
            if ok:
                return SendResult.OK
            if not self._is_image_error(data):
                return SendResult.FAILED
        return SendResult.PHOTO_FAILED

    def _send_to_chat(self, chat_id: str, html_text: str, image_url: Optional[str],
                      allow_text_fallback: bool,
                      local_image: Optional[tuple[str, bytes, str]] = None) -> SendResult:
        if image_url or local_image:
            fits = len(strip_tags(html_text)) <= CAPTION_LIMIT
            result = self._send_photo(chat_id, image_url, html_text if fits else None, local_image)
            if result is SendResult.OK:
                if fits:
                    return SendResult.OK
                return SendResult.OK if self._send_text(chat_id, html_text) else SendResult.FAILED
            if result is SendResult.PHOTO_FAILED and allow_text_fallback:
                LOG.warning("Rasm yuborilmadi — post rasmsiz yuboriladi.")
                return SendResult.OK if self._send_text(chat_id, html_text) else SendResult.FAILED
            return result
        return SendResult.OK if self._send_text(chat_id, html_text) else SendResult.FAILED

    def send(self, html_text: str, image_url: Optional[str] = None,
             allow_text_fallback: bool = True,
             local_image: Optional[tuple[str, bytes, str]] = None) -> SendResult:
        """Hech bo'lmaganda bitta kanalga yuborilsa OK (boshqa kanalda dublikat bo'lmasligi uchun)."""
        results = []
        for chat_id in self.chat_ids:
            res = self._send_to_chat(chat_id, html_text, image_url, allow_text_fallback, local_image)
            LOG.info("%s Telegram [%s]", "✅ Joylandi" if res is SendResult.OK else f"❌ {res.value}", chat_id)
            results.append(res)
        if SendResult.OK in results:
            return SendResult.OK
        if SendResult.PHOTO_FAILED in results:
            return SendResult.PHOTO_FAILED
        return SendResult.FAILED


# ──────────────────────────── ERTALABKI POST ────────────────────────────


def get_exchange_rates(session: requests.Session) -> str:
    try:
        rates = {r["Ccy"]: r["Rate"] for r in get_json(session, CBU_RATES_URL)}
        lines = [
            f"{emoji} <b>1 {ccy}</b> = {rates[ccy]} so'm"
            for ccy, emoji in (("USD", "💵"), ("EUR", "💶"), ("RUB", "💷"))
            if ccy in rates
        ]
        return "\n".join(lines) or "Valyuta kursi ma'lumotlari olinmadi."
    except (requests.RequestException, ValueError, KeyError, TypeError) as exc:
        LOG.warning("Valyuta kurslari olinmadi: %s", exc)
        return "Valyuta kursi ma'lumotlari olinmadi."


def get_weather(session: requests.Session) -> str:
    try:
        daily = get_json(session, WEATHER_URL)["daily"]
        t_max, t_min = daily["temperature_2m_max"][0], daily["temperature_2m_min"][0]
        rain = daily["precipitation_sum"][0] or 0
        rain_info = "🌧 Yog'ingarchilik kutilmoqda" if rain > 0.5 else "☀️ Ochiq va musaffo havo"
        return f"🌡 <b>Harorat:</b> {t_min}°C ... {t_max}°C\n{rain_info}"
    except (requests.RequestException, ValueError, KeyError, IndexError, TypeError) as exc:
        LOG.warning("Ob-havo olinmadi: %s", exc)
        return "Ob-havo ma'lumoti olinmadi."


def build_morning_post(session: requests.Session, now: datetime) -> str:
    return (
        "☀️ <b>Xayrli tong, aziz Do'stlik tumanliklar va Jizzaxliklar!</b>\n\n"
        f"📅 <b>Bugun:</b> {now.strftime('%d.%m.%Y')}\n\n\n"
        "🌦 <b>JIZZAX &amp; DO'STLIK TUMANIDA OB-HAVO:</b>\n\n"
        f"{get_weather(session)}\n\n\n"
        "🏛 <b>MARKAZIY BANK VALYUTA KURSLARI:</b>\n\n"
        f"{get_exchange_rates(session)}\n\n\n"
        "✨ <b>Kuningiz unumli va barakali o'tsin!</b>"
        f"{FOOTER_HTML}"
    )


def maybe_send_morning(publisher: TelegramPublisher, session: requests.Session,
                       state: dict[str, Any], now: datetime) -> None:
    today = now.strftime("%Y-%m-%d")
    in_window = now.hour == MORNING_HOUR and now.minute < MORNING_WINDOW_MIN
    if not in_window or state.get("morning_sent_date") == today:
        return
    LOG.info("Ertalabki ob-havo va valyuta posti yuborilmoqda...")
    if publisher.send(build_morning_post(session, now), None) is SendResult.OK:
        state["morning_sent_date"] = today
        save_json(DAILY_STATE_FILE, state)


# ──────────────────────────── REKLAMA BOSHQARUVI ────────────────────────────
#
# ads.json tuzilishi:
#   {"permanent": [...doimiy reklamalar...], "paid": [...muddatli (pullik) reklamalar...]}
#
# Reklama maydonlari:
#   id            — noyob nom (statistika uchun)
#   text          — post matni (yangiliklar kabi: **qalin**; telefon va @username o'zi bosiladigan bo'ladi)
#   image_file    — repo ichidagi rasm fayli, masalan "logoped.jpg" (private repo'da ham ishlaydi)  [tavsiya etiladi]
#   image_url     — rasm havolasi (faqat image_file bo'lmasa; repo public bo'lishi kerak)
#   active        — false bo'lsa vaqtincha o'chiriladi
#   start_date    — shu kundan boshlab chiqadi (YYYY-MM-DD), ixtiyoriy
#   expire_date   — shu kun OXIRIGACHA chiqadi (YYYY-MM-DD)
#   days          — start_date'dan boshlab necha kun (expire_date o'rniga): 7 = 1 hafta, 30 = ~1 oy
# Pullik (paid) reklamada expire_date yoki (start_date + days) majburiy. Muddati o'tgani avtomatik o'chiriladi.
#
# Navbat: pullik reklama bo'lsa — har PAID_SLOTS_PER_PERMANENT ta pullikdan keyin 1 ta doimiy (aralash aylanadi);
# pullik bo'lmasa — faqat doimiylar. Hisoblagich va navbat holati daily_state.json → "ads_state" da saqlanadi.


def _as_int(value: Any) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def _as_float(value: Any) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def _parse_date(value: Any) -> Optional[date]:
    try:
        return date.fromisoformat(str(value).strip())
    except ValueError:
        return None


def _ad_id(ad: dict[str, Any]) -> str:
    return str(ad.get("id") or ad.get("name") or ad.get("client") or str(ad.get("text", ""))[:20])


def _blank(value: Any) -> bool:
    return value is None or str(value).strip() == ""


def _effective_expire(ad: dict[str, Any]) -> Optional[date]:
    """Oxirgi amal qilish kuni: expire_date, yo'q bo'lsa start_date + days - 1. Noto'g'ri bo'lsa None."""
    if not _blank(ad.get("expire_date")):
        return _parse_date(ad["expire_date"])
    start = _parse_date(ad.get("start_date")) if not _blank(ad.get("start_date")) else None
    days = _as_int(ad.get("days"))
    if start is not None and days > 0:
        return start + timedelta(days=days - 1)
    return None


def load_ads() -> Optional[dict[str, Any]]:
    """
    ads.json'ni o'qiydi. Fayl yo'q bo'lsa — bo'sh tuzilma. Fayl buzuq bo'lsa (masalan, vergul unutilgan) —
    None qaytaradi va faylga TEGILMAYDI: bu safar reklama chiqmaydi, lekin ma'lumotlaringiz yo'qolmaydi.
    """
    p = Path(ADS_FILE)
    if not p.exists():
        return {"permanent": [], "paid": []}
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        LOG.error("%s o'qilmadi: %s — bu safar reklama chiqmaydi (fayl o'zgartirilmadi). JSON'ni tekshiring.",
                  ADS_FILE, exc)
        return None
    if not isinstance(data, dict):
        LOG.error("%s formati noto'g'ri (obyekt {...} bo'lishi kerak) — reklama o'tkazib yuboriladi.", ADS_FILE)
        return None
    for key in ("permanent", "paid"):
        if key not in data:
            data[key] = []
        elif not isinstance(data[key], list):
            LOG.error("%s ichida \"%s\" ro'yxat [...] bo'lishi kerak — reklama o'tkazib yuboriladi.", ADS_FILE, key)
            return None
    return data


def save_ads(ads: dict[str, Any]) -> bool:
    """ads.json'ni atomik yozadi (yarim yozilgan fayl qolmaydi)."""
    return save_json(ADS_FILE, ads)


def load_local_image(path: str) -> Optional[tuple[str, bytes, str]]:
    """Repo ichidagi rasmni o'qiydi (GitHub Actions repo'ni yuklab oladi, shuning uchun fayl mavjud)."""
    if not path:
        return None
    for candidate in (Path(path), Path(__file__).resolve().parent / path):
        if candidate.is_file():
            try:
                blob = candidate.read_bytes()
            except OSError as exc:
                LOG.warning("Rasm o'qilmadi (%s): %s", candidate, exc)
                return None
            if len(blob) > MAX_IMAGE_BYTES:
                LOG.warning("Rasm juda katta (%d bayt, limit ~9 MB): %s", len(blob), path)
                return None
            return candidate.name, blob, mimetypes.guess_type(candidate.name)[0] or "image/jpeg"
    LOG.warning("Rasm fayli topilmadi: %s (repo ildizida bormi? nomi harfma-harf to'g'rimi?)", path)
    return None


def _is_active(ad: Any, today: date, require_expiry: bool) -> bool:
    """Reklama bugun chiqishi mumkinmi: matni bor, o'chirilmagan, boshlanish sanasi kelgan, muddati o'tmagan."""
    if not isinstance(ad, dict) or not str(ad.get("text", "")).strip():
        return False
    if ad.get("active", True) is False:
        return False

    if not _blank(ad.get("start_date")):
        start = _parse_date(ad["start_date"])
        if start is None:
            LOG.warning("start_date noto'g'ri (YYYY-MM-DD bo'lishi kerak) — chiqarilmaydi: %s = %r",
                        _ad_id(ad), ad["start_date"])
            return False
        if today < start:
            return False  # hali boshlanmagan

    if _blank(ad.get("expire_date")) and _blank(ad.get("days")):
        if require_expiry:
            LOG.warning("Pullik reklamada expire_date (yoki start_date + days) yo'q — chiqarilmaydi: %s", _ad_id(ad))
        return not require_expiry

    expire = _effective_expire(ad)
    if expire is None:
        LOG.warning("Muddat noto'g'ri (expire_date=YYYY-MM-DD yoki start_date bilan birga days=son) — "
                    "chiqarilmaydi: %s", _ad_id(ad))
        return False
    return expire >= today  # expire kuni ham kun oxirigacha amal qiladi


def cleanup_expired_ads(today: date) -> int:
    """Muddati o'tgan pullik reklamalarni ads.json'dan o'chiradi. Noto'g'ri sanali yozuvlarga TEGILMAYDI."""
    ads = load_ads()
    if ads is None:
        return 0
    kept, removed = [], []
    for ad in ads["paid"]:
        expire = _effective_expire(ad) if isinstance(ad, dict) else None
        (removed if expire is not None and expire < today else kept).append(ad)
    if not removed:
        return 0
    ads["paid"] = kept
    if save_ads(ads):
        for ad in removed:
            LOG.info("Muddati o'tgan reklama o'chirildi: %s (oxirgi kun: %s)", _ad_id(ad), _effective_expire(ad))
    return len(removed)


def pick_ad(ads: dict[str, Any], ads_state: dict[str, Any], today: date) -> tuple[Optional[dict[str, Any]], str, int]:
    """
    Pullik va doimiy reklamalar aralash: pullik bo'lsa har PAID_SLOTS_PER_PERMANENT ta pullikdan keyin 1 ta doimiy.
    Faqat biri mavjud bo'lsa — o'sha. Har guruh ichida ro'yxat tartibida aylanadi.
    """
    paid = [a for a in ads["paid"] if _is_active(a, today, require_expiry=True)]
    permanent = [a for a in ads["permanent"] if _is_active(a, today, require_expiry=False)]

    if paid and permanent:
        cycle = PAID_SLOTS_PER_PERMANENT + 1
        kind = "permanent" if _as_int(ads_state.get("slot_no")) % cycle == cycle - 1 else "paid"
    elif paid:
        kind = "paid"
    elif permanent:
        kind = "permanent"
    else:
        return None, "", 0

    pool = paid if kind == "paid" else permanent
    idx = _as_int(ads_state.get(f"{kind}_index")) % len(pool)
    return pool[idx], kind, idx


def check_and_send_ad(publisher: TelegramPublisher, state: dict[str, Any], now: datetime) -> bool:
    """
    Shartlar bajarilsa 1 ta reklama yuboradi: (1) kamida POSTS_PER_AD yangilik o'tgan, (2) vaqt AD_HOURS ichida,
    (3) oxirgi reklamadan MIN_AD_INTERVAL_MIN daqiqa o'tgan. Muvaffaqiyatsiz bo'lsa hisoblagich saqlanadi.
    """
    ads_state = state.setdefault("ads_state", {})
    since = _as_int(ads_state.get("posts_since_ad"))
    if since < POSTS_PER_AD:
        LOG.info("Reklama navbati: %d/%d yangilik.", since, POSTS_PER_AD)
        return False
    if now.hour not in AD_HOURS:
        LOG.info("Reklama vaqti emas (%02d:%02d) — reklama faqat %02d:00–%02d:59 oralig'ida chiqadi.",
                 now.hour, now.minute, AD_HOURS.start, AD_HOURS.stop - 1)
        return False
    minutes_since_ad = (time.time() - _as_float(ads_state.get("last_ad_ts"))) / 60
    if minutes_since_ad < MIN_AD_INTERVAL_MIN:
        LOG.info("Oxirgi reklamadan %.0f daqiqa o'tdi (minimum %d) — reklama keyinga qoldirildi.",
                 minutes_since_ad, MIN_AD_INTERVAL_MIN)
        return False

    ads = load_ads()
    if ads is None:
        return False
    ad, kind, idx = pick_ad(ads, ads_state, now.date())
    if ad is None:
        LOG.info("Chiqariladigan faol reklama yo'q (ads.json'ni tekshiring).")
        return False

    # Reklama matni yangiliklar bilan bir xil formatda yoziladi: **qalin**, oddiy matn (HTML belgilari xavfsiz o'giriladi)
    ad_html = to_telegram_html(str(ad["text"]))
    local_image = load_local_image(str(ad.get("image_file") or "").strip())
    ad_image = None if local_image else (str(ad.get("image_url") or "").strip() or None)
    if (local_image or ad_image) and len(strip_tags(ad_html)) > CAPTION_LIMIT:
        LOG.warning("Reklama matni %d belgi — rasm ostiga sig'maydi (limit %d), rasm va matn ALOHIDA chiqadi. "
                    "Bitta post bo'lishi uchun qisqartiring: %s", len(strip_tags(ad_html)), CAPTION_LIMIT, _ad_id(ad))

    time.sleep(AD_DELAY_SEC)
    result = publisher.send(ad_html, ad_image, local_image=local_image)
    if result is not SendResult.OK:
        LOG.warning("Reklama yuborilmadi (%s): %s", result.value, _ad_id(ad))
        return False

    ads_state["posts_since_ad"] = 0
    ads_state[f"{kind}_index"] = idx + 1
    ads_state["slot_no"] = _as_int(ads_state.get("slot_no")) + 1
    ads_state["last_ad_ts"] = time.time()
    shown = ads_state.setdefault("shown", {})
    shown[_ad_id(ad)] = _as_int(shown.get(_ad_id(ad))) + 1  # mijozga hisobot berish uchun
    save_json(DAILY_STATE_FILE, state)
    LOG.info("📣 Reklama joylandi [%s]: %s (jami: %d marta)", kind, _ad_id(ad), shown[_ad_id(ad)])
    return True


# ──────────────────────────── ASOSIY OQIM ────────────────────────────


class Outcome(Enum):
    POSTED = "posted"
    SKIPPED = "skipped"    # qat'iy qaror: joylanmaydi (mos emas / rasm yo'q) — qayta ko'rilmaydi
    DEFERRED = "deferred"  # keyinroq qayta ko'riladi (masalan, AI vaqtincha ishlamayapti)
    FAILED = "failed"      # Telegram xatosi


def process_item(item: NewsItem, session: requests.Session, publisher: TelegramPublisher,
                 rewriter: AIRewriter, recent: RecentPosts) -> Outcome:
    if recent.is_duplicate(item.title):
        item.note = "takror (sarlavha o'xshash)"
        LOG.info("Takror (boshqa manbada allaqachon joylangan) — o'tkazib yuborildi: %s", item.title)
        return Outcome.SKIPPED

    enrich_item(session, item)

    image = item.image_url or DEFAULT_IMAGE_URL or None
    if not image and REQUIRE_IMAGE:
        item.note = "rasm topilmadi"
        LOG.info("Rasm topilmadi — o'tkazib yuborildi: %s", item.title)
        return Outcome.SKIPPED

    ai_text = rewriter.rewrite(item, recent.headlines())
    if ai_text == DUPLICATE:
        item.note = "takror (AI)"
        LOG.info("Takror (AI aniqladi) — o'tkazib yuborildi: %s", item.title)
        return Outcome.SKIPPED
    if ai_text == SKIP:
        item.note = "mavzu mos emas (AI)"
        LOG.info("Mavzu mos emas (AI) — o'tkazib yuborildi: %s", item.title)
        return Outcome.SKIPPED
    if ai_text is None and not looks_local(item):
        item.note = "AI ishlamadi, mahalliy emas"
        LOG.info("AI ishlamayapti va yangilik O'zbekistonga aloqador ko'rinmaydi — keyinga qoldirildi: %s", item.title)
        return Outcome.DEFERRED

    post = build_final_post(item, ai_text)
    item.headline = extract_headline(normalize_apostrophes(ai_text if ai_text else fallback_post_text(item)))
    result = publisher.send(post, image, allow_text_fallback=not REQUIRE_IMAGE)
    if result is SendResult.OK:
        item.note = "joylandi" if ai_text else "joylandi (AI'siz)"
        return Outcome.POSTED
    if result is SendResult.PHOTO_FAILED:
        item.note = "rasm yuborilmadi"
        LOG.warning("Rasm yuborib bo'lmadi — o'tkazib yuborildi: %s", item.title)
        return Outcome.SKIPPED
    item.note = "Telegram xatosi"
    return Outcome.FAILED


def publish_news(publisher: TelegramPublisher, rewriter: AIRewriter,
                 session: requests.Session, store: SeenStore, recent: RecentPosts,
                 deadline: Optional[float] = None) -> tuple[int, int]:
    posted = failures = evaluated = 0
    stats: collections.Counter = collections.Counter()
    for item in iter_candidates(session):
        if posted >= MAX_POSTS_PER_RUN or failures >= MAX_TELEGRAM_FAILURES or evaluated >= MAX_EVALUATE_PER_RUN:
            break
        if deadline is not None and time.monotonic() > deadline:
            LOG.warning("Ishga tushish vaqt chegarasi tugadi — qolgan yangiliklar keyingi safarga qoldirildi.")
            break
        if store.seen(item.dedup_keys):
            stats["allaqachon ko'rilgan"] += 1
            continue

        evaluated += 1
        LOG.info("Yangi yangilik: %s", item.title)
        try:
            outcome = process_item(item, session, publisher, rewriter, recent)
        except Exception:  # noqa: BLE001 — bitta "buzuq" yangilik navbatni abadiy to'sib qo'ymasin
            LOG.exception("Yangilikni qayta ishlashda kutilmagan xatolik — o'tkazib yuborildi: %s", item.title)
            outcome, item.note = Outcome.SKIPPED, "kutilmagan xatolik"
        stats[f"{outcome.value}: {item.note}"] += 1

        if outcome in (Outcome.POSTED, Outcome.SKIPPED):
            store.add(item.dedup_keys)
            store.save()  # har bir qarordan keyin saqlaymiz — keyingi xatolik dublikat keltirmasin
        if outcome is Outcome.POSTED:
            recent.add(item.title, item.headline)
            posted += 1
            time.sleep(POST_DELAY_SEC)
        elif outcome is Outcome.FAILED:
            failures += 1

    LOG.info("Yangiliklar tahlili: %s", dict(stats) if stats else "yangi yangilik topilmadi")
    return posted, failures


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")

    missing = [
        name for name, value in (
            ("TELEGRAM_BOT_TOKEN", TELEGRAM_BOT_TOKEN),
            ("TELEGRAM_CHAT_ID", TELEGRAM_CHAT_IDS),
        ) if not value
    ]
    if missing:
        LOG.error(
            "Quyidagi o'zgaruvchilar bo'sh yoki berilmagan: %s. Workflow'dagi `env:` blokini "
            "va Secrets nomlarini tekshiring (qiymat bo'sh bo'lsa ham shu xato chiqadi).",
            ", ".join(missing),
        )
        return 1

    session = build_session()
    publisher = TelegramPublisher(TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_IDS, session)
    rewriter = AIRewriter(GROQ_API_KEY, GROQ_MODELS)
    store = SeenStore(SEEN_FILE)
    state = load_json(DAILY_STATE_FILE, {})
    recent = RecentPosts(state)
    now = datetime.now(TZ)
    deadline = time.monotonic() + RUN_BUDGET_SEC

    try:
        maybe_send_morning(publisher, session, state, now)
    except Exception:  # noqa: BLE001 — ertalabki postdagi xato yangiliklarni to'xtatmasin
        LOG.exception("Ertalabki postda xatolik — yangiliklar davom etadi.")
    try:
        cleanup_expired_ads(now.date())
    except Exception:  # noqa: BLE001
        LOG.exception("Reklamalarni tozalashda xatolik — davom etiladi.")

    minutes_since_last = (time.time() - float(state.get("last_post_ts", 0))) / 60
    if minutes_since_last < MIN_POST_INTERVAL_MIN:
        LOG.info("Oxirgi postdan %.0f daqiqa o'tdi (minimum %d) — bu safar post joylanmaydi.",
                 minutes_since_last, MIN_POST_INTERVAL_MIN)
        return 0

    posted, failures = publish_news(publisher, rewriter, session, store, recent, deadline)
    store.save()
    if posted:
        state["last_post_ts"] = time.time()
        ads_state = state.setdefault("ads_state", {})
        ads_state["posts_since_ad"] = _as_int(ads_state.get("posts_since_ad")) + posted
        save_json(DAILY_STATE_FILE, state)
        try:
            check_and_send_ad(publisher, state, now)
        except Exception:  # noqa: BLE001 — reklama xatosi yangilik postiga ta'sir qilmasin
            LOG.exception("Reklama yuborishda kutilmagan xatolik.")

    LOG.info("Yakun: %d ta post joylandi, %d ta xatolik.", posted, failures)
    return 1 if failures and not posted else 0


if __name__ == "__main__":
    sys.exit(main())
