#!/usr/bin/env python3
"""
DO'STLIK BOZOR | YANGILIKLAR — Telegram yangiliklar boti.

Oqim:
  1. (06:00-08:59 Toshkent vaqti bilan, kuniga 1 marta) ob-havo + valyuta posti.
  2. gov.uz/jizzax va respublika RSS manbalaridan yangi xabarlarni yig'ish.
  3. Groq AI orqali qayta yozish (modellar zanjiri + zaxira format).
  4. Telegram kanal(lar)ga xavfsiz joylash (HTML parse, avtomatik fallback).

Muhit o'zgaruvchilari:
  TELEGRAM_BOT_TOKEN  (majburiy)
  TELEGRAM_CHAT_ID    (majburiy; bir nechta kanal bo'lsa vergul bilan: "@kanal1,@kanal2")
  GROQ_API_KEY        (ixtiyoriy; bo'lmasa AI'siz zaxira format ishlatiladi)
  GROQ_MODELS         (ixtiyoriy; vergul bilan, birinchisi asosiy model)
"""
from __future__ import annotations

import html
import json
import logging
import os
import re
import sys
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Iterator, Optional
from urllib.parse import urljoin
from zoneinfo import ZoneInfo

import feedparser
import requests
from bs4 import BeautifulSoup
from groq import Groq
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ──────────────────────────── SOZLAMALAR ────────────────────────────

LOG = logging.getLogger("newsbot")

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_IDS = [
    c.strip() for c in os.environ.get("TELEGRAM_CHAT_ID", "").split(",") if c.strip()
]
GROQ_API_KEY = os.environ.get("GROQ_API_KEY", "").strip()

# Eslatma: "llama3-8b-8192" va "mixtral-8x7b-32768" Groq'da to'xtatilgan, shu sababli
# ular o'rniga hozirgi modellar qo'yilgan. Ro'yxatni GROQ_MODELS orqali kodsiz o'zgartirish mumkin.
DEFAULT_GROQ_MODELS = [
    "llama-3.3-70b-versatile",
    "llama-3.1-8b-instant",
    "openai/gpt-oss-20b",
]
GROQ_MODELS = [
    m.strip() for m in os.environ.get("GROQ_MODELS", "").split(",") if m.strip()
] or DEFAULT_GROQ_MODELS

TZ = ZoneInfo("Asia/Tashkent")  # GitHub Actions UTC'da ishlaydi — vaqt albatta Toshkent bo'yicha olinsin

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
SEEN_LIMIT = 1000  # fayl cheksiz o'smasligi uchun

MAX_POSTS_PER_RUN = 2
ENTRIES_PER_FEED = 6
MAX_TELEGRAM_FAILURES = 2  # ketma-ket shuncha xato bo'lsa, ishni to'xtatamiz
MORNING_HOURS = range(6, 9)  # 06:00 – 08:59

CAPTION_LIMIT = 1024
MESSAGE_LIMIT = 4096
GROQ_TIMEOUT = 30.0

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

# ──────────────────────────── YORDAMCHI FUNKSIYALAR ────────────────────────────


def build_session() -> requests.Session:
    """Retry va backoff'li HTTP sessiya (faqat GET uchun; POST takrorlanishi Telegram'da qo'lda boshqariladi)."""
    retry = Retry(
        total=3,
        connect=3,
        read=3,
        backoff_factor=1.5,
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
    """Atomik yozish: avval vaqtinchalik faylga, keyin os.replace — yarim yozilgan fayl qolmaydi."""
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
    """Matnni gap oxirida (iloji bo'lsa) qisqartirish."""
    if len(text) <= limit:
        return text
    cut = text[:limit]
    idx = max(cut.rfind(". "), cut.rfind("! "), cut.rfind("? "))
    if idx > limit * 0.5:
        return cut[: idx + 1]
    return cut.rsplit(" ", 1)[0] + "…"


_SOURCE_NAMES = re.compile(r"#?\b(?:kun|daryo|qalampir|gazeta|gov)\.?\s?uz\b", re.IGNORECASE)
_SOURCE_LINE = re.compile(r"^\s*(?:manba|источник|source|via)\s*[:\-–].*$", re.IGNORECASE | re.MULTILINE)


def scrub_sources(text: str) -> str:
    """AI e'tiborsizlik qilib manba nomini yozib yuborsa ham, uni olib tashlaydi."""
    text = _SOURCE_LINE.sub("", text)
    text = _SOURCE_NAMES.sub("", text)
    return re.sub(r"[ \t]{2,}", " ", text)


_BOLD = re.compile(r"\*\*(.+?)\*\*")


def to_telegram_html(text: str) -> str:
    """
    Oddiy/markdown-ga o'xshash matnni Telegram HTML'ga xavfsiz aylantiradi.
    Eski 'Markdown' rejimidagi asosiy xato manbai shu edi: AI matnidagi `_`, `*`, `[` belgilari
    (masalan, @Dostlik_jizzax1) 'can't parse entities' xatosini keltirib chiqarardi.
    """
    text = text.replace("\r\n", "\n")
    text = re.sub(r"^\s{0,3}#{1,6}\s+", "", text, flags=re.MULTILINE)  # "### Sarlavha" -> "Sarlavha" (#xeshteg tegilmaydi)
    text = re.sub(r"^\s*[*\-]\s+", "• ", text, flags=re.MULTILINE)
    text = html.escape(text, quote=False)
    text = _BOLD.sub(r"<b>\1</b>", text)
    text = text.replace("*", "")
    text = re.sub(r"\n{4,}", "\n\n\n", text)
    return text.strip()


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


# ──────────────────────────── MA'LUMOT MANBALARI ────────────────────────────


@dataclass
class NewsItem:
    uid: str
    title: str
    summary: str
    image_url: Optional[str] = None

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
    """RSS'ni session orqali (timeout + retry bilan) yuklab, feedparser'ga tayyor kontent beradi."""
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
    for entry in feed.entries[:ENTRIES_PER_FEED]:
        title = (entry.get("title") or "").strip()
        uid = entry.get("id") or entry.get("link") or ""
        if not title or not uid:
            continue
        summary = clean_html(entry.get("summary") or entry.get("description") or "")
        items.append(NewsItem(uid=uid, title=title, summary=summary, image_url=extract_image_url(entry)))
    return items


def _fetch_article_text(session: requests.Session, url: str) -> str:
    """Maqola sahifasidan qisqa matn (og:description yoki paragraflar). AI uydirma qilmasligi uchun kerak."""
    try:
        res = session.get(url, timeout=15)
        res.raise_for_status()
    except requests.RequestException as exc:
        LOG.warning("Maqola sahifasi ochilmadi (%s): %s", url, exc)
        return ""
    soup = BeautifulSoup(res.content, "html.parser")
    meta = soup.find("meta", attrs={"property": "og:description"})
    paragraphs = [p.get_text(" ", strip=True) for p in soup.find_all("p")]
    body = " ".join(p for p in paragraphs if len(p) > 40)
    if body:
        return re.sub(r"\s+", " ", body)[:1500]
    if meta and meta.get("content"):
        return clean_html(meta["content"])
    return ""


def fetch_gov_item(session: requests.Session) -> Optional[NewsItem]:
    """gov.uz/jizzax bo'limidagi eng so'nggi yangilik (sarlavha + maqola matni)."""
    try:
        res = session.get(GOV_NEWS_URL, timeout=15)
        res.raise_for_status()
    except requests.RequestException as exc:
        LOG.warning("gov.uz/jizzax yuklanmadi: %s", exc)
        return None

    soup = BeautifulSoup(res.content, "html.parser")
    # Bo'limning o'ziga (…/jizzax/news) emas, aynan maqolaga (…/jizzax/news/<id>) olib boruvchi havola kerak
    for a in soup.find_all("a", href=re.compile(r"/jizzax/news/[^/?#]+")):
        title = a.get_text(" ", strip=True)
        if len(title) < 15:
            continue
        link = urljoin("https://gov.uz", a["href"])
        return NewsItem(uid=link, title=title, summary=_fetch_article_text(session, link))

    LOG.warning("gov.uz/jizzax'da maqola havolasi topilmadi (sayt tuzilishi o'zgargan bo'lishi mumkin).")
    return None


def iter_candidates(session: requests.Session) -> Iterator[NewsItem]:
    """Lazy generator: limitga yetilgach keyingi manbalar umuman so'ralmaydi."""
    gov = fetch_gov_item(session)
    if gov:
        yield gov
    for feed_url in RSS_FEEDS:
        yield from fetch_rss_items(session, feed_url)


# ──────────────────────────── AI (GROQ) ────────────────────────────

SYSTEM_PROMPT = (
    "Siz 'DO'STLIK BOZOR | YANGILIKLAR' Telegram kanalining tajribali jurnalistisiz. "
    "Kanal Jizzax viloyati va Do'stlik tumani aholisiga mo'ljallangan. Faqat o'zbek (lotin) tilida yozing."
)

USER_PROMPT = """Quyidagi yangilik asosida Telegram uchun professional post tayyorlang.

Qoidalar:
1. Hech qanday manba nomini (Kun.uz, Daryo.uz, Gazeta.uz, Qalampir.uz, Gov.uz va h.k.) yozmang.
2. Sarlavha diqqatni tortsin, 1-2 ta mos emoji bilan; sarlavhani **qalin** qiling.
3. Abzaslar orasida bo'sh qator qoldiring. Hajmi: taxminan 500-900 belgi.
4. Faqat berilgan faktlardan foydalaning. Raqam, ism, sana va joy nomlarini o'zgartirmang, yangi fakt o'ylab topmang.
5. Oxirida 2-3 ta mos xeshteg (masalan: #Jizzax #Dostlik #Yangiliklar).
6. Markdown sarlavhalari (#), havolalar va kod bloklaridan foydalanmang.
7. FAQAT tayyor post matnini qaytaring — izoh yoki kirish so'zlarisiz.

Yangilik sarlavhasi: {title}
Yangilik matni: {summary}
"""


class AIRewriter:
    """Groq orqali qayta yozish: modellar zanjiri, timeout, circuit-breaker."""

    MAX_FAILED_ROUNDS = 2  # ketma-ket shuncha marta barcha modellar yiqilsa, qolgan ishga tushishda AI o'chiriladi

    def __init__(self, api_key: str, models: list[str]) -> None:
        self.models = models
        self.client: Optional[Groq] = None
        self.failed_rounds = 0
        if api_key:
            try:
                self.client = Groq(api_key=api_key, timeout=GROQ_TIMEOUT, max_retries=2)
            except Exception as exc:  # noqa: BLE001
                LOG.error("Groq klienti yaratilmadi: %s", exc)
        else:
            LOG.warning("GROQ_API_KEY topilmadi — AI'siz zaxira format ishlatiladi.")

    @property
    def available(self) -> bool:
        return self.client is not None and self.failed_rounds < self.MAX_FAILED_ROUNDS

    @staticmethod
    def _sanitize(text: str) -> Optional[str]:
        text = re.sub(r"^```[a-zA-Z]*\n?|```$", "", (text or "").strip(), flags=re.MULTILINE).strip()
        text = scrub_sources(text).strip()
        if len(text) < 40 or len(text) > 3000:
            return None
        return text

    def rewrite(self, item: NewsItem) -> Optional[str]:
        if not self.available:
            return None
        summary = item.summary or "(matn mavjud emas — faqat sarlavhadan foydalaning, yangi faktlar qo'shmang)"
        prompt = USER_PROMPT.format(title=item.title, summary=summary)

        for model in self.models:
            try:
                resp = self.client.chat.completions.create(  # type: ignore[union-attr]
                    model=model,
                    messages=[
                        {"role": "system", "content": SYSTEM_PROMPT},
                        {"role": "user", "content": prompt},
                    ],
                    temperature=0.4,
                    max_tokens=1200,
                )
                text = self._sanitize(resp.choices[0].message.content)
                if text:
                    self.failed_rounds = 0
                    LOG.info("AI javobi tayyor (model: %s)", model)
                    return text
                LOG.warning("Model %s yaroqsiz (bo'sh/juda qisqa/juda uzun) javob qaytardi.", model)
            except Exception as exc:  # noqa: BLE001 — Groq SDK turli xil xatolik sinflarini beradi
                LOG.warning("Groq model %s xatoligi [%s]: %s", model, type(exc).__name__, exc)
                time.sleep(1.5)

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
    body = ai_text if ai_text else fallback_post_text(item)
    return to_telegram_html(body) + FOOTER_HTML


# ──────────────────────────── TELEGRAM ────────────────────────────

_ERROR_HINTS = (
    ("chat not found", "chat_id noto'g'ri yoki bot kanalga qo'shilmagan (kanalda ADMIN bo'lishi shart)."),
    ("bot was kicked", "Bot kanaldan chiqarib yuborilgan."),
    ("not enough rights", "Botda kanalga post yuborish huquqi yo'q (admin huquqlarini tekshiring)."),
    ("unauthorized", "TELEGRAM_BOT_TOKEN noto'g'ri yoki bekor qilingan."),
    ("can't parse entities", "Formatlash xatosi — matn oddiy ko'rinishda qayta yuboriladi."),
    ("wrong file identifier", "Rasm URL'i yaroqsiz — post rasmsiz yuboriladi."),
    ("failed to get http url content", "Telegram rasmni yuklab ola olmadi — post rasmsiz yuboriladi."),
    ("message is too long", "Matn 4096 belgidan uzun."),
)


class TelegramPublisher:
    def __init__(self, token: str, chat_ids: list[str], session: requests.Session) -> None:
        self.token = token
        self.chat_ids = chat_ids
        self.session = session

    # -- past darajali so'rov ------------------------------------------------
    def _redact(self, text: str) -> str:
        return text.replace(self.token, "***") if self.token else text

    def _call(self, method: str, payload: dict[str, Any], attempts: int = 3) -> tuple[bool, dict[str, Any]]:
        url = f"https://api.telegram.org/bot{self.token}/{method}"
        data: dict[str, Any] = {}
        for attempt in range(1, attempts + 1):
            try:
                res = self.session.post(url, data=payload, timeout=20)
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

            if code == 429:  # flood limit
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

    # -- yuborish bosqichlari ---------------------------------------------------
    def _send_text(self, chat_id: str, html_text: str) -> bool:
        payload = {
            "chat_id": chat_id,
            "text": html_text,
            "parse_mode": "HTML",
            "disable_web_page_preview": "true",
        }
        ok, data = self._call("sendMessage", payload)
        if ok:
            return True
        if self._is_parse_error(data):
            plain = strip_tags(html_text)[:MESSAGE_LIMIT]
            ok, _ = self._call("sendMessage", {"chat_id": chat_id, "text": plain, "disable_web_page_preview": "true"})
        return ok

    def _send_photo(self, chat_id: str, image_url: str, caption_html: Optional[str]) -> bool:
        payload: dict[str, Any] = {"chat_id": chat_id, "photo": image_url}
        if caption_html:
            payload.update(caption=caption_html, parse_mode="HTML")
        ok, data = self._call("sendPhoto", payload)
        if not ok and caption_html and self._is_parse_error(data):
            ok, _ = self._call("sendPhoto", {"chat_id": chat_id, "photo": image_url,
                                             "caption": strip_tags(caption_html)[:CAPTION_LIMIT]})
        return ok

    def _send_to_chat(self, chat_id: str, html_text: str, image_url: Optional[str]) -> bool:
        if image_url:
            fits = len(strip_tags(html_text)) <= CAPTION_LIMIT
            if self._send_photo(chat_id, image_url, html_text if fits else None):
                # Matn sig'masa: rasm alohida, matn alohida (caption kesilib, footer yo'qolmaydi)
                return True if fits else self._send_text(chat_id, html_text)
            LOG.warning("Rasm yuborilmadi — post rasmsiz yuboriladi.")
        return self._send_text(chat_id, html_text)

    def send(self, html_text: str, image_url: Optional[str] = None) -> bool:
        """Hech bo'lmaganda bitta kanalga muvaffaqiyatli yuborilsa True (dublikat bo'lmasligi uchun)."""
        results = []
        for chat_id in self.chat_ids:
            ok = self._send_to_chat(chat_id, html_text, image_url)
            LOG.info("%s Telegram [%s]", "✅ Joylandi" if ok else "❌ Joylanmadi", chat_id)
            results.append(ok)
        return any(results)


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
    if now.hour not in MORNING_HOURS or state.get("morning_sent_date") == today:
        return
    LOG.info("Ertalabki ob-havo va valyuta posti yuborilmoqda...")
    if publisher.send(build_morning_post(session, now), None):
        state["morning_sent_date"] = today  # faqat muvaffaqiyatli yuborilgandagina belgilanadi
        save_json(DAILY_STATE_FILE, state)


# ──────────────────────────── ASOSIY OQIM ────────────────────────────


def publish_news(publisher: TelegramPublisher, rewriter: AIRewriter,
                 session: requests.Session, store: SeenStore) -> tuple[int, int]:
    posted = failures = 0
    for item in iter_candidates(session):
        if posted >= MAX_POSTS_PER_RUN or failures >= MAX_TELEGRAM_FAILURES:
            break
        if store.seen(item.dedup_keys):
            continue

        LOG.info("Yangi yangilik: %s", item.title)
        post = build_final_post(item, rewriter.rewrite(item))

        if publisher.send(post, item.image_url):
            store.add(item.dedup_keys)
            store.save()  # har bir muvaffaqiyatdan keyin — keyingi xatolik dublikat keltirmasin
            posted += 1
        else:
            failures += 1
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
    now = datetime.now(TZ)

    maybe_send_morning(publisher, session, state, now)
    posted, failures = publish_news(publisher, rewriter, session, store)
    store.save()

    LOG.info("Yakun: %d ta post joylandi, %d ta xatolik.", posted, failures)
    # Faqat xatolik bo'lib, birorta ham post chiqmasa Actions "qizil" bo'ladi — muammo sezilib qoladi
    return 1 if failures and not posted else 0


if __name__ == "__main__":
    sys.exit(main())
