import os
import re
import json
import requests
import feedparser
from datetime import datetime
from bs4 import BeautifulSoup
from groq import Groq

# Maxfiy kalitlarni GitHub Secrets'dan olish
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID")
GROQ_API_KEY = os.environ.get("GROQ_API_KEY")

groq_client = Groq(api_key=GROQ_API_KEY)

# Respublika yangilik manbalari
RSS_FEEDS = [
    "https://kun.uz/news/rss",
    "https://daryo.uz/rss/",
    "https://qalampir.uz/uz/rss",
    "https://www.gazeta.uz/uz/rss/"
]

SEEN_FILE = "seen_news.json"
DAILY_STATE_FILE = "daily_state.json"

def load_json(filename):
    if os.path.exists(filename):
        try:
            with open(filename, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {} if "state" in filename else []
    return {} if "state" in filename else []

def save_json(filename, data):
    with open(filename, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

def extract_image_url(entry):
    if "media_content" in entry and entry.media_content:
        return entry.media_content[0].get("url")
    if "enclosures" in entry and entry.enclosures:
        for enc in entry.enclosures:
            if enc.get("type", "").startswith("image/"):
                return enc.get("href")
    if "summary" in entry:
        soup = BeautifulSoup(entry.summary, "html.parser")
        img = soup.find("img")
        if img and img.get("src"):
            return img.get("src")
    return None

def clean_html(text):
    soup = BeautifulSoup(text, "html.parser")
    return soup.get_text()

def fetch_gov_jizzax_news():
    """Jizzax viloyati hokimligi rasmiy portali (gov.uz/uz/jizzax)dan yangilik olish"""
    try:
        url = "https://gov.uz/uz/jizzax/news"
        headers = {'User-Agent': 'Mozilla/5.0'}
        res = requests.get(url, headers=headers, timeout=10)
        if res.status_code == 200:
            soup = BeautifulSoup(res.content, 'html.parser')
            news_card = soup.find('a', href=re.compile(r'/jizzax/news'))
            if news_card:
                title = news_card.get_text(strip=True)
                link = news_card.get('href', '')
                if link and not link.startswith('http'):
                    link = f"https://gov.uz{link}"
                return title, link
    except Exception as e:
        print(f"gov.uz/uz/jizzax saytidan xabar olishda xatolik: {e}")
    return None, None

def get_exchange_rates():
    """Markaziy Bankdan valyuta kurslarini olish"""
    try:
        res = requests.get("https://cbu.uz/uz/arkhiv-kursov-valyut/json/", timeout=10)
        rates = res.json()
        usd = next(r for r in rates if r["Ccy"] == "USD")["Rate"]
        eur = next(r for r in rates if r["Ccy"] == "EUR")["Rate"]
        rub = next(r for r in rates if r["Ccy"] == "RUB")["Rate"]
        return f"💵 **1 USD** = {usd} so'm\n💶 **1 EUR** = {eur} so'm\n💷 **1 RUB** = {rub} so'm"
    except Exception:
        return "Valyuta kursi ma'lumotlari olinmadi."

def get_jizzax_weather():
    """Jizzax / Do'stlik tumani ob-havosini olish"""
    try:
        url = "https://api.open-meteo.com/v1/forecast?latitude=40.1158&longitude=67.8422&daily=temperature_2m_max,temperature_2m_min,precipitation_sum&timezone=Asia%2FTashkent"
        res = requests.get(url, timeout=10).json()
        temp_max = res["daily"]["temperature_2m_max"][0]
        temp_min = res["daily"]["temperature_2m_min"][0]
        rain = res["daily"]["precipitation_sum"][0]
        
        rain_info = "🌧 Yog'ingarchilik kutilmoqda" if rain > 0.5 else "☀️ Ochiq va musaffo havo"
        return f"🌡 **Harorat:** {temp_min}°C ... {temp_max}°C\n{rain_info}"
    except Exception:
        return "Ob-havo ma'lumoti olinmadi."

def send_morning_update():
    """Toza va bo'shliqlar bilan ajratilgan rasmsiz ertalabki post"""
    today_str = datetime.now().strftime("%Y-%m-%d")
    rates_text = get_exchange_rates()
    weather_text = get_jizzax_weather()
    
    post = (
        f"☀️ **Xayrli tong, aziz Do'stlik tumanliklar va Jizzaxliklar!**\n\n"
        f"📅 **Bugun:** {today_str}\n\n\n"
        f"🌦 **JIZZAX & DO'STLIK TUMANIDA OB-HAVO:**\n\n"
        f"{weather_text}\n\n\n"
        f"🏛 **MARKAZIY BANK VALYUTA KURSLARI:**\n\n"
        f"{rates_text}\n\n\n"
        f"✨ **Kuningiz unumli va barakali o'tsin!**\n\n\n"
        f"🛒 **Bizning kanallar:**\n"
        f"📢 @dostlik_bozor2 | @Dostlik_jizzax1\n\n"
        f"👨‍💻 **Reklama joylash uchun:**\n"
        f"👉 @shohrux_1308\n"
        f"👉 @azizjon_dev"
    )
    
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": post,
        "parse_mode": "Markdown",
        "disable_web_page_preview": True
    }
    requests.post(url, data=payload)

def rewrite_with_groq(title, summary):
    prompt = f"""
Siz "DO'STLIK BOZOR | YANGILIKLAR" Telegram kanali uchun tajribali jurnalistsiz.
Kanalimiz Jizzax viloyati va Do'stlik tumani aholisiga mo'ljallangan.
Quyidagi yangilikni tahlil qiling va Telegram kanali uchun professional post tayyorlang.

Qoidalar:
1. Hech qanday manba nomini (masalan: Kun.uz, Daryo.uz, Gov.uz) yozmang va eslatib o'tmang.
2. Sarlavha diqqatni tortadigan bo'lsin (1-2 ta mos emoji bilan).
3. Matn abzaslari orasida bo'sh joy qoldiring (har bir abzas alohida tursin).
4. Post oxiriga 2-3 ta mos xashtag qo'shing (masalan: #Jizzax #Dostlik #Yangiliklar).
5. FAQAT tayyor post matnini qaytaring.

Yangilik sarlavhasi: {title}
Yangilik matni: {summary}
"""
    try:
        response = groq_client.chat.completions.create(
            model="qwen-2.5-32b",
            messages=[{"role": "user", "content": prompt}],
            temperature=0.5,
            max_tokens=700
        )
        return response.choices[0].message.content.strip()
    except Exception as e:
        print(f"AI qayta ishlashda xatolik: {e}")
        return f"⚡️ **{title}**\n\n{summary}"

def build_final_post(ai_text):
    footer = (
        "\n\n\n"
        "🛒 **Bizning kanallar:**\n"
        "📢 @dostlik_bozor2 | @Dostlik_jizzax1\n\n"
        "👨‍💻 **Reklama joylash uchun:**\n"
        "👉 @shohrux_1308\n"
        "👉 @azizjon_dev"
    )
    return ai_text + footer

def send_telegram_post(text, image_url):
    if image_url:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendPhoto"
        payload = {
            "chat_id": TELEGRAM_CHAT_ID,
            "caption": text[:1024],
            "parse_mode": "Markdown",
            "photo": image_url
        }
    else:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        payload = {
            "chat_id": TELEGRAM_CHAT_ID,
            "text": text,
            "parse_mode": "Markdown",
            "disable_web_page_preview": True
        }
    res = requests.post(url, data=payload)
    return res.status_code == 200

def main():
    seen_news = set(load_json(SEEN_FILE))
    daily_state = load_json(DAILY_STATE_FILE)
    
    current_hour = datetime.now().hour
    today_str = datetime.now().strftime("%Y-%m-%d")

    # Ertalabki soat 06:00 va 08:00 oralig'ida faqat 1 marta yuboriladi
    if 6 <= current_hour <= 8 and daily_state.get("morning_sent_date") != today_str:
        print("Ertalabki ob-havo va valyuta posti yuborilmoqda...")
        send_morning_update()
        daily_state["morning_sent_date"] = today_str
        save_json(DAILY_STATE_FILE, daily_state)

    new_posts_count = 0

    # 1. Jizzax viloyati hokimligi (gov.uz/uz/jizzax) sayti tekshiruvi
    gov_title, gov_link = fetch_gov_jizzax_news()
    if gov_title and gov_link not in seen_news:
        print(f"Jizzax hokimiyatidan yangi xabar: {gov_title}")
        context_msg = "Jizzax viloyat hokimligi rasmiy xabari"
        ai_post = rewrite_with_groq(gov_title, context_msg)
        final_post = build_final_post(ai_post)
        if send_telegram_post(final_post, None):
            seen_news.add(gov_link)
            new_posts_count += 1

    # 2. Respublika RSS yangiliklari
    for feed_url in RSS_FEEDS:
        if new_posts_count >= 2:
            break
        print(f"Manba tekshirilmoqda: {feed_url}")
        feed = feedparser.parse(feed_url)
        
        for entry in feed.entries[:4]:
            news_id = entry.get("id") or entry.get("link")
            title = entry.get("title", "").strip()
            clean_title_key = re.sub(r'\W+', '', title.lower())[:30]
            
            if news_id in seen_news or clean_title_key in seen_news:
                continue
                
            raw_summary = entry.get("summary") or entry.get("description", "")
            summary = clean_html(raw_summary)
            image_url = extract_image_url(entry)

            print(f"Yangi yangilik topildi: {title}")
            ai_post = rewrite_with_groq(title, summary)
            final_post = build_final_post(ai_post)
            
            success = send_telegram_post(final_post, image_url)
            
            if success:
                print("Kanalga muvaffaqiyatli joylandi!")
                seen_news.add(news_id)
                seen_news.add(clean_title_key)
                new_posts_count += 1
                if new_posts_count >= 2:
                    break

    save_json(SEEN_FILE, list(seen_news))

if __name__ == "__main__":
    main()
