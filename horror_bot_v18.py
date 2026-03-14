"""
╔══════════════════════════════════════════════════════════════════╗
║                  👁  HORROR BOT v19.0  👁                       ║
║         Маскировка: бот-переводчик                              ║
║  Установка:  pip install pyTelegramBotAPI requests gTTS groq     ║
║  Запуск:     python horror_bot_v19.py                           ║
║  Гл. admin:  /admingo  (личка)                                  ║
╚══════════════════════════════════════════════════════════════════╝

ИЗМЕНЕНИЯ v19.0:
  ① ИИ в группе: хамит, но всегда выполняет задания
  ② ГОЛОС: после каждого ответа ИИ в группе — автоголосовое
  ③ КНОПКА «🤖 Добавить ИИ» в меню игр — ИИ заменяет игроков
  ④ МАФИЯ: исправлена + ИИ-игрок участвует (голосует, убивает)
  ⑤ ИИ в ЛС: «само зло», следит, пугает, отвечает на /ai
  ⑥ ОПТИМИЗАЦИЯ: thread-pool, кеш, cleanup старых сессий
  ⑦ НОВОЕ: /ai [вопрос] команда в группе и ЛС

ИЗМЕНЕНИЯ v17.0 (баг-фикс + новые фичи):
  ① ГРУППА: исправлена def group_game_kb — кнопки «Игры» работают
  ② ГРУППА: кнопка «🔤 Язык» — выбор языка через inline прямо в чате
  ③ ГРУППА: кнопка «🔤 Язык» есть на всех стадиях страха в ЛС
  ④ УРОВЕНЬ СТРАХА: смена стадии раз в 15 минут (STAGE_SEC=900)
  ⑤ ЗАГАДКА: больше не удаляется после первой неправильной попытки
  ⑥ ЧАТ-РЕЖИМ: заглушённые жертвы не получают чат-сообщения
  ⑦ ПЕРЕВОД В ГРУППЕ: использует выбранный язык пользователя
  ⑧ adm_max: исправлен спам-чек при пакетных атаках
  ⑨ НОВОЕ: хоррор-приветствие новых участников группы
  ⑩ НОВОЕ: 👻 Шёпот — бот иногда тихо пишет одному участнику лично
  ⑪ НОВОЕ: /help и 📊 Мой счёт в группе
  ⑫ НОВОЕ: кнопки «📊 Мой счёт» и «❓ Помощь» в группе
  ⑬ ОПТИМИЗАЦИЯ: thread-safe _kb_cache.clear(), _spam_mark fix
"""

import telebot, requests, threading, time, random, datetime, re, os
import tempfile, logging, traceback, signal, sys
from concurrent.futures import ThreadPoolExecutor
from telebot.types import (ReplyKeyboardMarkup, KeyboardButton,
                            ReplyKeyboardRemove, InlineKeyboardMarkup,
                            InlineKeyboardButton)

# ── Groq AI ──────────────────────────────────────────────────
try:
    from groq import Groq as GroqClient
    _GROQ_AVAILABLE = True
except ImportError:
    _GROQ_AVAILABLE = False

try:
    from cerebras.cloud.sdk import Cerebras as CerebrasClient
    _CEREBRAS_AVAILABLE = True
except ImportError:
    _CEREBRAS_AVAILABLE = False

logging.basicConfig(
    level=logging.WARNING,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("bot.log", encoding="utf-8"),
              logging.StreamHandler()]
)
log = logging.getLogger("horror")

try:
    from gtts import gTTS
    VOICE_ENABLED = True
except ImportError:
    VOICE_ENABLED = False
    log.warning("gTTS не установлен. pip install gTTS")

# ══════════════════════════════════════════════════════════════
#  КОНФИГУРАЦИЯ  — читается из переменных окружения
#  Задайте в Railway/Render:
#    BOT_TOKEN        — токен вашего Telegram-бота
#    WEATHER_API_KEY  — ключ openweathermap.org (бесплатно)
#    ADMIN_ID         — ваш Telegram ID (числовой)
# ══════════════════════════════════════════════════════════════
BOT_TOKEN        = os.environ.get("BOT_TOKEN", "")
WEATHER_API_KEY  = os.environ.get("WEATHER_API_KEY", "")
ADMIN_ID         = int(os.environ.get("ADMIN_ID", "0"))
GROQ_API_KEY     = os.environ.get("GROQ_API_KEY", "")
CEREBRAS_API_KEY = os.environ.get("CEREBRAS_API_KEY", "")
AI_BACKEND       = os.environ.get("AI_BACKEND", "auto")  # "groq", "cerebras", "auto"
GROUP_AUTO_VOICE = os.environ.get("GROUP_AUTO_VOICE", "1") == "1"  # автоголосовое в группе

STAGE_SEC        = 900             # секунд между стадиями (15 минут)
HORROR_DELAY_SEC = 45              # задержка первого хоррора
SPY_FORWARD      = True            # пересылать сообщения жертв admin'ам

# ══════════════════════════════════════════════════════════════
#  ХРАНИЛИЩЕ  (с блокировкой для thread-safety)
# ══════════════════════════════════════════════════════════════
_lock    = threading.Lock()
users    = {}    # uid → dict
games    = {}    # uid → dict
adm_state= {}    # admin_uid → {step, target_uid}
admins   = set() # все admin'ы (включая ADMIN_ID)

# Пул потоков для фоновых задач (не плодим бесконечные Thread'ы)
_pool = ThreadPoolExecutor(max_workers=32, thread_name_prefix="horror")

_kb_cache = {}   # кеш клавиатур

# ── Anti-spam: cooldown между хоррор-тиками ──────────────────
# Минимальный интервал (сек) между ЛЮБЫМИ сообщениями одному пользователю
_SPAM_MIN_INTERVAL = 8          # не менее 8 сек между сообщениями
_last_msg_time: dict = {}       # uid → timestamp последнего отправленного сообщения
_spam_lock = threading.Lock()

def _spam_check(uid) -> bool:
    """Возвращает True если можно отправить сообщение (cooldown прошёл). Обновляет timestamp."""
    with _spam_lock:
        now = time.time()
        last = _last_msg_time.get(uid, 0)
        if now - last < _SPAM_MIN_INTERVAL:
            return False
        _last_msg_time[uid] = now
        return True

def _spam_mark(uid):
    """Обновляет время последнего сообщения только если нет недавней записи."""
    with _spam_lock:
        now = time.time()
        # Не перебиваем timestamp если он уже свежий (установлен spam_check)
        if now - _last_msg_time.get(uid, 0) >= 1:
            _last_msg_time[uid] = now

# ── v11 хранилища ──────────────────────────────────────────
# _scenarios определён ниже (встроенные сценарии)
_daily_done = {}  # uid → date_str  — когда выполнено ежедневное задание
_squad_mode = {}  # uid → partner_uid  — совместный квест
_rand_event_thr = None  # фоновый поток случайных событий
_stage_history  = {}  # uid → [(timestamp, stage), ...]  — для графа
_scheduled_attacks = []  # [{uid, func, fire_at}, ...]  — таймер-атаки
_auto_mode  = set()  # uid'ы жертв с включённым авто-режимом

# ── v12 хранилища ──────────────────────────────────────────
_stage_frozen   = {}   # uid → unfreeze_time  — заморозка стадии
_group_games    = {}   # chat_id → {game, data}  — групповые игры
_group_users    = {}   # chat_id → set(uid)  — участники в группах
_group_card_story = {}  # chat_id → {scene, players, ...} — карточная история в группе
_ai_intercept: dict = {}  # uid → {"timer", "context", "chat_id"} — admin пишет за ИИ
_group_awaiting = {}   # chat_id → ("weather"|"translate"|"ai", uid)

# ── v13 хранилища ──────────────────────────────────────────
# Мафия между обычными пользователями (ЛС)
# _mafia_lobby и _mafia_player удалены — используется _maf и _maf_uid
# Групповая мафия
_group_mafia    = {}   # chat_id → game_state
# Карточная история (visual-novel style)
_card_story     = {}   # uid → {story_id, scene, character, inventory}

def is_admin(uid):
    return uid == ADMIN_ID or uid in admins

def is_root_admin(uid):
    """Главный и единственный неограниченный администратор."""
    return uid == ADMIN_ID

def is_stage_frozen(uid):
    """Проверяет, заморожена ли стадия у пользователя."""
    freeze_until = _stage_frozen.get(uid)
    if freeze_until and time.time() < freeze_until:
        return True
    if uid in _stage_frozen:
        del _stage_frozen[uid]
    return False

def send_group(chat_id, text, kb=None):
    """Отправляет сообщение в группу."""
    if kb:
        _safe_call(bot.send_message, chat_id, text, reply_markup=kb)
    else:
        _safe_call(bot.send_message, chat_id, text)

def U(uid):
    """Потокобезопасное создание/получение профиля пользователя."""
    with _lock:
        if uid not in users:
            users[uid] = dict(
                name=None, age=None, city=None, interests=[],
                pet=None, job=None, fear=None, sleep_time=None,
                color=None, food=None, music=None, phone=None,
                lang_pair="ru|en",
                stage=0, horror_active=False,
                stopped=False, muted=False,
                username=None,
                msg_count=0, score=0,
                custom_queue=[],
                msg_history=[],   # полная история (макс 100)
                banned=False,
                spy=True,
                translate_mode=False,  # True = ждём текст для перевода (одно сообщение)
                ai_mode=False,  # True = режим диалога с ИИ в ЛС
            )
        return users[uid]

def FC(u):
    """Счётчик собранных фактов о пользователе."""
    c = sum(1 for k in ("name","age","city","pet","job","fear","sleep_time","phone") if u.get(k))
    c += min(len(u.get("interests",[])), 3)
    return c

def night():  return datetime.datetime.now().hour >= 22 or datetime.datetime.now().hour <= 5
def dnight(): return 0 <= datetime.datetime.now().hour <= 4

def P(t, u):
    """Персонализация шаблона данными пользователя."""
    try:
        return t.format(
            name    = u.get("name")     or "ты",
            age     = u.get("age")      or "...",
            city    = u.get("city")     or "твоём городе",
            interest= (u.get("interests") or ["это"])[0],
            pet     = u.get("pet")      or "питомец",
            fear    = u.get("fear")     or "темнота",
            color   = u.get("color")    or "чёрный",
            food    = u.get("food")     or "еда",
            music   = u.get("music")    or "музыка",
            phone   = u.get("phone")    or "твой телефон",
            job     = u.get("job")      or "учёба",
        )
    except Exception:
        return t

# ══════════════════════════════════════════════════════════════
#  ИНИЦИАЛИЗАЦИЯ БОТА
# ══════════════════════════════════════════════════════════════
def make_bot():
    return telebot.TeleBot(
        BOT_TOKEN,
        parse_mode=None,
        threaded=False,
    )

bot = make_bot()

# ══════════════════════════════════════════════════════════════
#  БЕЗОПАСНАЯ ОТПРАВКА
# ══════════════════════════════════════════════════════════════
def _safe_call(fn, *args, retries=3, **kwargs):
    for attempt in range(retries):
        try:
            return fn(*args, **kwargs)
        except telebot.apihelper.ApiTelegramException as e:
            code = e.error_code
            if code == 429:
                wait = int(e.result_json.get("parameters",{}).get("retry_after",5))
                time.sleep(wait + 1)
            elif code in (400, 403):
                return None   # бот заблокирован или невалидный запрос — не ретраим
            else:
                time.sleep(2 ** attempt)
        except requests.exceptions.ConnectionError:
            time.sleep(3)
        except Exception:
            log.debug(traceback.format_exc())
            time.sleep(1)
    return None

def send(uid, text, kb=None):
    _spam_mark(uid)
    if kb:
        _safe_call(bot.send_message, uid, text, reply_markup=kb)
    else:
        _safe_call(bot.send_message, uid, text)

def sgif(uid, url):
    _safe_call(bot.send_animation, uid, url)

def sphoto(uid, src):
    _safe_call(bot.send_photo, uid, src)

def svoice_file(uid, path):
    try:
        with open(path, "rb") as f:
            _safe_call(bot.send_voice, uid, f)
    except Exception:
        pass

def scontact(uid, phone, name):
    _safe_call(bot.send_contact, uid, phone_number=phone, first_name=name)

# ══════════════════════════════════════════════════════════════
#  ШПИОНАЖ — пересылка сообщений admin'ам
# ══════════════════════════════════════════════════════════════
def spy_forward(uid, text):
    if not SPY_FORWARD:
        return
    u = U(uid)
    # ИСПРАВЛЕНО: было `if not u.get("spy", True)` — инверсия логики
    if not u.get("spy", True):
        return
    uname  = u.get("username") or "?"
    name   = u.get("name")     or "?"
    header = f"👁 [{uid}] @{uname} ({name}):\n"
    msg    = header + text
    for aid in (admins | {ADMIN_ID}):
        if aid != uid:
            _safe_call(bot.send_message, aid, msg)

# ══════════════════════════════════════════════════════════════
#  ПЕРЕВОДЧИК + ПОГОДА
# ══════════════════════════════════════════════════════════════
LANG_NAMES = {
    "ru|en":    "🇷🇺 Русский → 🇬🇧 Английский",
    "en|ru":    "🇬🇧 Английский → 🇷🇺 Русский",
    "ru|de":    "🇷🇺 Русский → 🇩🇪 Немецкий",
    "ru|fr":    "🇷🇺 Русский → 🇫🇷 Французский",
    "ru|es":    "🇷🇺 Русский → 🇪🇸 Испанский",
    "ru|zh-CN": "🇷🇺 Русский → 🇨🇳 Китайский",
    "ru|ja":    "🇷🇺 Русский → 🇯🇵 Японский",
    "ru|ar":    "🇷🇺 Русский → 🇸🇦 Арабский",
}

_translate_cache = {}  # (text, lang_pair) -> result

def translate(text, lang_pair="ru|en"):
    """Переводит текст через MyMemory API. Кешируем повторные запросы."""
    key = (text[:100], lang_pair)
    if key in _translate_cache:
        return _translate_cache[key]
    try:
        r = requests.get(
            "https://api.mymemory.translated.net/get",
            params={"q": text, "langpair": lang_pair},
            timeout=8
        ).json()
        result = r.get("responseData", {}).get("translatedText", "")
        # Проверяем что перевод реально отличается от оригинала
        if (result and
                "INVALID LANGUAGE PAIR" not in result and
                "QUERY LENGTH LIMIT" not in result and
                result.strip().lower() != text.strip().lower()):
            _translate_cache[key] = result
            # Ограничиваем кеш 200 записями
            if len(_translate_cache) > 200:
                oldest = next(iter(_translate_cache))
                del _translate_cache[oldest]
            return result
        return None
    except requests.exceptions.Timeout:
        log.debug("Translate timeout")
        return None
    except Exception:
        log.debug(traceback.format_exc())
        return None

def get_weather(city):
    try:
        r = requests.get(
            "http://api.openweathermap.org/data/2.5/weather",
            params=dict(q=city, appid=WEATHER_API_KEY, units="metric", lang="ru"),
            timeout=5
        ).json()
        if r.get("cod") != 200:
            return None
        t  = r["main"]["temp"];  fl = r["main"]["feels_like"]
        hm = r["main"]["humidity"]
        ds = r["weather"][0]["description"]
        ws = r.get("wind", {}).get("speed", "?")
        return (f"🌤 Погода в {r['name']}:\n"
                f"🌡 {t}°C (ощущается {fl}°C)\n"
                f"💧 Влажность: {hm}%   💨 Ветер: {ws} м/с\n"
                f"☁️ {ds.capitalize()}")
    except Exception:
        return None

# ══════════════════════════════════════════════════════════════
#  КЛАВИАТУРЫ  (с кешированием)
# ══════════════════════════════════════════════════════════════
def KB(stage=0):
    """Клавиатура меняется с ростом стадии хоррора."""
    key = f"kb_{stage}"
    if key in _kb_cache:
        return _kb_cache[key]
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    if stage < 2:
        # 0-1: дружелюбный режим
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌤 Погода"),       KeyboardButton("🎮 Игры"))
        k.add(KeyboardButton("🎲 Угадай"),       KeyboardButton("🧠 Викторина"))
        k.add(KeyboardButton("✏️ Виселица"),     KeyboardButton("🎭 Загадка"))
        k.add(KeyboardButton("🔮 Предсказание"), KeyboardButton("📖 Факт"))
        k.add(KeyboardButton("🗓 Задание дня"),  KeyboardButton("🏆 Мой рейтинг"))
        k.add(KeyboardButton("🔫 Мафия"),        KeyboardButton("🤖 ИИ"))
        k.add(KeyboardButton("❓ Помощь"),        KeyboardButton("🙂 О боте"))
    elif stage < 4:
        # 2-3: нарастающая тьма
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌑 Погода"),       KeyboardButton("🎮 Игры"))
        k.add(KeyboardButton("🎲 Угадай"),       KeyboardButton("🔮 Предсказание"))
        k.add(KeyboardButton("👁 ..."),          KeyboardButton("🗓 Задание дня"))
        k.add(KeyboardButton("🔫 Мафия"),        KeyboardButton("🤖 ИИ"))
        k.add(KeyboardButton("🏆 Мой рейтинг"))
    else:
        # 4+: полная тьма
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌑 Погода"),       KeyboardButton("🩸 Игры"))
        k.add(KeyboardButton("👁 Кто ты?"),      KeyboardButton("🗓 Задание дня"))
        k.add(KeyboardButton("🔫 Мафия"),        KeyboardButton("🤖 ИИ"))
        k.add(KeyboardButton("🏆 Мой рейтинг"),  KeyboardButton("💀 /stop"))
    _kb_cache[key] = k
    return k

def KB_ADM():
    """Клавиатура ГЛАВНОГО admin'а — неограниченные возможности."""
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("👥 Жертвы"),               KeyboardButton("📊 Полная статистика"))
    k.add(KeyboardButton("💀 Ужас всем"),            KeyboardButton("🛑 Стоп всем"))
    k.add(KeyboardButton("▶️ Рестарт всем"),         KeyboardButton("🔇 Тишина всем"))
    k.add(KeyboardButton("🔊 Звук всем"),            KeyboardButton("📤 Рассылка всем"))
    k.add(KeyboardButton("⚙️ Выбрать жертву"),       KeyboardButton("📋 Список ID"))
    k.add(KeyboardButton("💬 Чат 3 мин"),            KeyboardButton("💬 Чат 10 мин"))
    k.add(KeyboardButton("🔕 Стоп чат"),             KeyboardButton("👥 Чат деанон"))
    k.add(KeyboardButton("🏆 Лидеры страха"),        KeyboardButton("🎬 Все сценарии"))
    k.add(KeyboardButton("🗓 Ежедн. задание всем"),  KeyboardButton("🎲 Случай. событие"))
    # ── ROOT ONLY ──
    k.add(KeyboardButton("👑 Мои со-admin'ы"),       KeyboardButton("➕ Добавить admin'а"))
    k.add(KeyboardButton("➖ Убрать admin'а"),        KeyboardButton("👥 Группы (управление)"))
    k.add(KeyboardButton("🚫 Забанить жертву"),      KeyboardButton("✅ Разбанить жертву"))
    k.add(KeyboardButton("📡 Отправить по ID"),      KeyboardButton("🗑 Сбросить всех"))
    k.add(KeyboardButton("🤖 ИИ: Groq"),             KeyboardButton("🤖 ИИ: Cerebras"))
    k.add(KeyboardButton("🤖 ИИ: Авто"),             KeyboardButton("🤖 ИИ: Статус"))
    k.add(KeyboardButton("🤖 ИИ пишет за меня"))
    k.add(KeyboardButton("🔙 Выйти из бога"))
    return k

def KB_ADM_SUB():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("👥 Жертвы"),           KeyboardButton("📊 Статистика"))
    k.add(KeyboardButton("💀 Ужас всем"),        KeyboardButton("🛑 Стоп всем"))
    k.add(KeyboardButton("▶️ Рестарт всем"),     KeyboardButton("🔇 Тишина всем"))
    k.add(KeyboardButton("🔊 Звук всем"),        KeyboardButton("📤 Рассылка всем"))
    k.add(KeyboardButton("⚙️ Выбрать жертву"),   KeyboardButton("📋 Список ID"))
    k.add(KeyboardButton("💬 Чат 3 мин"),        KeyboardButton("💬 Чат 10 мин"))
    k.add(KeyboardButton("🔕 Стоп чат"),         KeyboardButton("👥 Чат деанон"))
    k.add(KeyboardButton("🏆 Лидеры страха"),     KeyboardButton("🗓 Ежедн. задание всем"))
    k.add(KeyboardButton("🤖 ИИ: Groq"),          KeyboardButton("🤖 ИИ: Cerebras"))
    k.add(KeyboardButton("🤖 ИИ: Авто"),          KeyboardButton("🤖 ИИ: Статус"))
    k.add(KeyboardButton("🔙 Выйти из бога"))
    return k

def KB_VIC():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("📝 Текст"),              KeyboardButton("🎬 Гифка"))
    k.add(KeyboardButton("🖼 Фото"),               KeyboardButton("📹 Видео"))
    k.add(KeyboardButton("⚡ Скример"),            KeyboardButton("☠️ Макс-ужас"))
    k.add(KeyboardButton("🌊 Волна паники"),       KeyboardButton("🕯 Ритуал"))
    k.add(KeyboardButton("💬 Диалог-ловушка"),     KeyboardButton("😴 Спящий режим"))
    k.add(KeyboardButton("⬆️ Стадия +1"),          KeyboardButton("⬇️ Стадия -1"))
    k.add(KeyboardButton("🔇 Заглушить"),          KeyboardButton("🔊 Включить"))
    k.add(KeyboardButton("📱 Взлом телефона"),     KeyboardButton("🎙 Голос от него"))
    k.add(KeyboardButton("📞 Фейк-звонок"),        KeyboardButton("📲 Реальный звонок"))
    k.add(KeyboardButton("💀 Таймер смерти"),      KeyboardButton("📨 Вернуть сообщения"))
    k.add(KeyboardButton("📷 Фейк-галерея"),       KeyboardButton("🚫 Фейк-бан"))
    k.add(KeyboardButton("👻 Фейк-уход"),          KeyboardButton("👁 Шпионаж ВКЛ"))
    k.add(KeyboardButton("🙈 Шпионаж ВЫКЛ"),       KeyboardButton("📜 Вся история"))
    k.add(KeyboardButton("📍 Геолокация"),         KeyboardButton("📲 Скан телефона"))
    k.add(KeyboardButton("👥 Призраки"),           KeyboardButton("📂 Скан файлов"))
    k.add(KeyboardButton("💬 Умное эхо"),          KeyboardButton("📡 Потеря сигнала"))
    k.add(KeyboardButton("🕒 Режим 3AM"),          KeyboardButton("🔐 TG Security"))
    k.add(KeyboardButton("🕯 Экзорцист"),          KeyboardButton("📺 Трансляция"))
    k.add(KeyboardButton("📡 GPS трекинг"),        KeyboardButton("🌐 Взлом Wi-Fi"))
    k.add(KeyboardButton("🔔 Уведомления"),        KeyboardButton("🗳 Опрос"))
    k.add(KeyboardButton("⚡ Глитч-атака"),        KeyboardButton("🪞 Зеркало"))
    k.add(KeyboardButton("🫀 Сердцебиение"),       KeyboardButton("🗑 Удалённое сообщение"))
    k.add(KeyboardButton("🤝 Совместный квест"),   KeyboardButton("🔁 Авто-режим ВКЛ"))
    k.add(KeyboardButton("⏹ Авто-режим ВЫКЛ"),    KeyboardButton("🎬 Сценарий"))
    k.add(KeyboardButton("👁 ИИ-атака СТАРТ"),    KeyboardButton("🛑 ИИ-атака СТОП"))
    k.add(KeyboardButton("⏰ Таймер-атака"),       KeyboardButton("📊 Граф стадий"))
    k.add(KeyboardButton("💾 Создать сценарий"),   KeyboardButton("🗑 Удалить сценарий"))
    k.add(KeyboardButton("✏️ Редактировать данные"), KeyboardButton("❄️ Заморозить стадию"))
    k.add(KeyboardButton("🔓 Разморозить стадию"), KeyboardButton("📋 Инфо"))
    k.add(KeyboardButton("🤖 ИИ пишет за меня"),  KeyboardButton("🔄 Сбросить"))
    k.add(KeyboardButton("🔙 Назад"))
    return k

def KB_LANG():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for code, name in LANG_NAMES.items():
        k.add(KeyboardButton(name))
    k.add(KeyboardButton("↩️ Назад"))
    return k

def game_kb(choices):
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for label, _ in choices:
        k.add(KeyboardButton(label))
    k.add(KeyboardButton("❌ Выйти из игры"))
    return k

def adm_kb(uid):
    return KB_ADM() if uid == ADMIN_ID else KB_ADM_SUB()

# ══════════════════════════════════════════════════════════════
#  ГОЛОСОВЫЕ СООБЩЕНИЯ (gTTS)
# ══════════════════════════════════════════════════════════════
VOICE_TEXTS = [
    "я вижу тебя.", "обернись.", "я здесь.", "ты не один.",
    "я знаю где ты.", "не закрывай телефон.",
    "я слышу тебя.", "я рядом. всегда.", "не смотри в угол.",
]
VOICE_TEXTS_PERSONAL = [
    "я знаю тебя, {name}.", "{name}. обернись.",
    "из {city} не убежишь, {name}.",
    "твой страх {fear} — это я, {name}.",
    "{name}. я вижу тебя через камеру.",
    "{name}. я буду здесь всегда.",
    "ты думаешь что один, {name}. нет.",
]

def _send_tts(uid, text):
    if not VOICE_ENABLED:
        send(uid, f"🎙 {text}"); return
    path = None
    try:
        with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tmp:
            path = tmp.name
        # slow=True + tld="com.au" даёт более низкий мрачный голос
        gTTS(text=text, lang="ru", slow=True, tld="com").save(path)
        svoice_file(uid, path)
        os.unlink(path)
    except Exception:
        try:
            if path:
                gTTS(text=text, lang="ru", slow=True).save(path)
                svoice_file(uid, path)
                os.unlink(path)
            else:
                send(uid, f"🎙 {text}")
        except Exception:
            send(uid, f"🎙 {text}")

def send_voice_msg(uid, text):
    _pool.submit(_send_tts, uid, text)

# ══════════════════════════════════════════════════════════════
#  СИСТЕМНЫЕ УВЕДОМЛЕНИЯ / «ВЗЛОМ»
# ══════════════════════════════════════════════════════════════
SYS_NOTIFICATIONS = [
    "⚠️ СИСТЕМНОЕ УВЕДОМЛЕНИЕ\n\nОбнаружен несанкционированный доступ.\nIP: 192.168.{r1}.{r2}\nВремя: {time}\n\nНе отключайте устройство.",
    "🔴 ПРЕДУПРЕЖДЕНИЕ БЕЗОПАСНОСТИ\n\nВаши данные передаются на внешний сервер.\nНачало: {time}\nФайлов скопировано: {n}\n\nОстановить невозможно.",
    "💻 СИСТЕМНОЕ СООБЩЕНИЕ\n\nКто-то вошёл в ваш Telegram.\nУстройство: Android Unknown\nМестоположение: {city}\nВремя: {time}",
    "🛡 НАРУШЕНИЕ БЕЗОПАСНОСТИ\n\nВаша камера активирована удалённо.\nЗапись начата: {time}\nПередача: активна\n\nОтключение невозможно.",
    "📡 ALERT: DEVICE COMPROMISED\n\nRoot access granted.\nFiles accessed: {n}\nCamera: STREAMING\nMicrophone: ACTIVE\nTime: {time}",
    "⚠️ TELEGRAM SECURITY\n\nАккаунт @{username} используется с нового устройства.\nЛокация: {city}\nЕсли это не вы — уже поздно.",
    "🔓 ВЗЛОМ ЗАВЕРШЁН\n\nДоступ к устройству получен.\nСкопировано контактов: {n}\nИстория чатов: загружена\nФотографии: {n2} шт.",
    "💀 КРИТИЧЕСКАЯ ОШИБКА\n\nПроцесс com.telegram.hack запущен.\nПамять читается.\nВремя до завершения: {count} сек.",
]

def make_sys_notify(u):
    now = datetime.datetime.now().strftime("%H:%M:%S")
    return random.choice(SYS_NOTIFICATIONS).format(
        r1=random.randint(1,254), r2=random.randint(1,254),
        time=now, n=random.randint(47,312), n2=random.randint(200,1800),
        count=random.randint(10,60), city=u.get("city") or "Unknown",
        username=u.get("username") or "user"
    )

GALLERY_MSGS = [
    "📷 я открыл твою галерею.\n\n{n} фото.\nя всё посмотрел.\nты красиво фотографируешь.",
    "🖼 галерея доступна.\n\n{n} изображений.\nесть несколько интересных.\nты бы не хотел чтобы их видели другие.",
    "📸 твои фото.\n\nвсе {n} штук.\nнекоторые... я запомню.\n\nты не закрыл доступ. жаль.",
    "🔍 я изучил твои фотографии, {name}.\n\n{n} снимков.\nесть те где ты один.\nи те где ты не знал что тебя снимают.",
    "📷 доступ к галерее получен.\n\nпоследнее фото сделано {days} дней назад.\nты тогда был в {city}.\nя видел.",
]

def make_gallery_msg(u):
    n    = random.randint(150, 2400)
    days = random.randint(1, 14)
    tmpl = random.choice(GALLERY_MSGS)
    return P(tmpl.format(n=n, days=days, name=u.get("name") or "ты",
                         city=u.get("city") or "твоём городе"), u)

# ══════════════════════════════════════════════════════════════
#  ЗВОНКИ
# ══════════════════════════════════════════════════════════════
def real_call(uid):
    u = U(uid)
    caller = random.choice(["Неизвестный", "???", "Не бери трубку", "Он", "👁 Наблюдатель"])
    def _run():
        scontact(uid, "+70000000000", caller)
        time.sleep(1)
        if VOICE_ENABLED:
            _send_tts(uid, "ты не берёшь трубку. напрасно.")
        else:
            send(uid, "📞 ты не берёшь трубку...")
        time.sleep(2)
        scontact(uid, "+70000000000", caller)
        time.sleep(2)
        send(uid, P("я дозвонюсь, {name}. рано или поздно.", u))
    _pool.submit(_run)

def fake_call_sequence(uid):
    u = U(uid)
    caller = random.choice(["Неизвестный", "???", "Обернись", "Он", "Не бери трубку", "👁"])
    def _run():
        send(uid, "📞 входящий звонок...")
        time.sleep(1)
        scontact(uid, "+70000000000", caller)
        time.sleep(3)
        send(uid, "ты не взял трубку.")
        time.sleep(2)
        send(uid, "я подожду.")
        time.sleep(3)
        send(uid, "📞 входящий звонок...")
        time.sleep(1)
        scontact(uid, "+70000000000", caller)
        time.sleep(2)
        send(uid, "...")
        time.sleep(3)
        send(uid, P("в следующий раз возьми трубку, {name}.", u))
    _pool.submit(_run)

# ══════════════════════════════════════════════════════════════
#  ФЕЙК-БАН / УХОД / ТАЙМЕР / ЭХО
# ══════════════════════════════════════════════════════════════
def fake_ban_sequence(uid):
    u = U(uid)
    def _run():
        send(uid, "⚠️ Telegram\n\nВаш аккаунт заблокирован за нарушение правил.\nОбжалование невозможно.")
        time.sleep(3)
        send(uid, "Этот чат будет удалён через 10 секунд.")
        # Показываем только 5, 3, 1 — не спамим каждую секунду
        for i in [9, 5, 3, 1]:
            time.sleep(2); send(uid, str(i) + "...")
        time.sleep(2); send(uid, "🗑 Чат удалён.")
        time.sleep(4); send(uid, "...")
        time.sleep(3); send(uid, "шучу.", kb=KB(u["stage"]))
        time.sleep(2); send(uid, P("или нет, {name}?", u))
    _pool.submit(_run)

def fake_leave_sequence(uid):
    u = U(uid)
    def _run():
        send(uid, "я ухожу.")
        time.sleep(3); send(uid, "прощай.")
        time.sleep(4); send(uid, ".")
        time.sleep(5); send(uid, "..")
        time.sleep(4); send(uid, "...")
        time.sleep(6); send(uid, "ты скучал?")
        time.sleep(2); send(uid, P("я никуда не уходил, {name}.", u))
        time.sleep(1); send(uid, "я никогда не ухожу. 👁")
    _pool.submit(_run)

def death_timer(uid, seconds=30):
    u = U(uid)
    def _run():
        send(uid, P("💀 {name}.", u))
        time.sleep(2); send(uid, "ты уже мёртв.")
        time.sleep(2); send(uid, "просто ещё не знаешь.")
        time.sleep(2); send(uid, f"осталось {seconds} секунд.")
        time.sleep(max(seconds // 2, 5))
        if u.get("stopped"): return
        send(uid, f"⏳ {seconds // 2}...")
        time.sleep(max(seconds // 2, 5))
        if u.get("stopped"): return
        send(uid, "0\n.\n..\n...\n....\nОБЕРНИСЬ")
        time.sleep(2)
        send_screamer(uid)
        time.sleep(2)
        send(uid, P("это была шутка, {name}.\nили нет.\n👁", u))
    _pool.submit(_run)

def echo_back_history(uid):
    u = U(uid)
    hist = u.get("msg_history", [])
    def _run():
        send(uid, "я всё помню.")
        time.sleep(2); send(uid, "вот что ты писал мне:")
        time.sleep(2)
        sample = random.sample(hist, min(len(hist), 5)) if hist else []
        if not sample:
            send(uid, "каждое слово.\nкаждую букву.\nты ничего не удалишь."); return
        for m in sample:
            time.sleep(random.uniform(1.5, 3.5)); send(uid, f"«{m}»")
        time.sleep(2); send(uid, "я храню это навсегда. 👁")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════
#  НОВЫЕ ФУНКЦИИ v10: ГЕОЛОКАЦИЯ / СКАН / ПРИЗРАКИ / ФАЙЛЫ / 3AM
# ══════════════════════════════════════════════════════════════

def fake_geolocation(uid):
    """Отправляет фейковую геолокацию жертвы."""
    u = U(uid)
    city = u.get("city") or "твоём городе"
    lat = round(random.uniform(48.0, 59.0), 4)
    lon = round(random.uniform(30.0, 50.0), 4)
    acc = random.randint(8, 30)
    def _run():
        msg = (
            "📍 ЛОКАЦИЯ ОБНАРУЖЕНА\n\n"
            "Город: " + str(city) + "\n"
            "Координаты: " + str(lat) + ", " + str(lon) + "\n"
            "Точность: " + str(acc) + " м\n\n"
            "я рядом."
        )
        send(uid, msg)
        time.sleep(random.uniform(3, 7))
        send(uid, P("...{name}. я уже иду.", u))
    _pool.submit(_run)


def fake_phone_scan(uid):
    """Фейковый скан устройства."""
    u = U(uid)
    models = [
        "Samsung Galaxy S23", "Xiaomi Redmi Note 12", "iPhone 14",
        "Huawei P50", "POCO X5 Pro", "Realme 11", "OnePlus 11",
    ]
    model = u.get("phone") or random.choice(models)
    battery = random.randint(12, 89)
    wifi = random.choice(["подключён", "активен", "ОБНАРУЖЕН"])
    files = random.randint(1200, 8900)
    def _run():
        msg = (
            "📱 Сканирование устройства...\n\n"
            "Модель: " + str(model) + "\n"
            "Батарея: " + str(battery) + "%\n"
            "Wi-Fi: " + str(wifi) + "\n"
            "Камера: активна\n"
            "Файлов найдено: " + str(files)
        )
        send(uid, msg)
        time.sleep(random.uniform(4, 8))
        send(uid, "камера уже работает.")
        time.sleep(2)
        send(uid, P("я вижу тебя, {name}. прямо сейчас.", u))
    _pool.submit(_run)


_GHOST_NAMES = [
    "user_481", "user_277", "user_039", "user_814", "user_563",
    "user_192", "user_730", "user_447", "user_658", "user_321",
]
GHOST_MSGS = [
    ["ты тоже это видишь?", "он пишет мне тоже", "что происходит..."],
    ["не отвечай ему", "он знает где ты", "я боюсь"],
    ["выйди из чата", "ВЫЙДИ ИЗ ЧАТА", "уже поздно"],
    ["помогите", "кто-нибудь здесь?", "..."],
    ["я видел его", "он стоял у моей двери", "теперь его нет"],
    ["не смотри на экран", "НЕ СМОТРИ НА ЭКРАН", "ты уже смотришь"],
    ["он в каждом телефоне", "мы все здесь", "ты следующий"],
]


def fake_ghost_users(uid):
    """Иллюзия других пользователей в чате."""
    u = U(uid)
    msgs = random.choice(GHOST_MSGS)
    def _run():
        for m in msgs:
            ghost = random.choice(_GHOST_NAMES)
            time.sleep(random.uniform(2.5, 5.0))
            send(uid, "👤 " + ghost + ":\n" + m)
        time.sleep(random.uniform(3, 6))
        send(uid, P("...теперь только ты и я, {name}.", u))
    _pool.submit(_run)


def fake_file_scan(uid):
    """Фейковое чтение файлов с устройства."""
    u = U(uid)
    uname = u.get("name") or "user"
    n_photos = random.randint(200, 2800)
    n_videos  = random.randint(10, 300)
    r1 = random.randint(100, 999)
    r2 = random.randint(100, 999)
    r3 = random.randint(100, 999)
    r4 = random.randint(1, 9)
    r5 = random.randint(1000, 9999)
    file_list = [
        "/DCIM/photo_" + str(r1) + ".jpg",
        "/DCIM/photo_" + str(r2) + ".jpg",
        "/Telegram/video_" + str(r3) + ".mp4",
        "/Download/passwords.txt",
        "/Download/notes_" + str(r4) + ".txt",
        "/WhatsApp/Media/IMG_" + str(r5) + ".jpg",
        "/Documents/" + uname + "_personal.pdf",
    ]
    shown = random.sample(file_list, min(5, len(file_list)))
    def _run():
        send(uid, "📂 scanning storage...")
        time.sleep(random.uniform(3, 5))
        send(uid, "\n".join(shown))
        time.sleep(random.uniform(2, 4))
        msg = (
            "доступ получен.\n\n"
            "фото: " + str(n_photos) + "\n"
            "видео: " + str(n_videos) + "\n"
            "...\n\nинтересно."
        )
        send(uid, msg)
        time.sleep(3)
        send(uid, P("особенно /Download/passwords.txt, {name}.", u))
    _pool.submit(_run)


def smart_echo_history(uid):
    """Умное эхо — 'N минут назад ты писал: ...'"""
    u = U(uid)
    hist = u.get("msg_history", [])
    if not hist:
        echo_back_history(uid)
        return
    def _run():
        send(uid, "я помню всё.")
        time.sleep(2)
        sample = random.sample(hist, min(3, len(hist)))
        for m in sample:
            mins = random.randint(2, 47)
            if mins == 1:
                suffix = "у"
            elif 2 <= mins <= 4:
                suffix = "ы"
            else:
                suffix = ""
            time.sleep(random.uniform(2, 4))
            send(uid, str(mins) + " минут" + suffix + " назад ты написал:\n\n«" + m + "»\n\nправда?")
        time.sleep(3)
        send(uid, P("я храню каждое слово, {name}. навсегда. 👁", u))
    _pool.submit(_run)


def signal_loss(uid):
    """Фейковая потеря сигнала."""
    u = U(uid)
    def _run():
        send(uid, "📡 соединение нестабильно...")
        time.sleep(2)
        for _ in range(random.randint(2, 4)):
            glitch = random.choice([
                "ERR_CONNECTION_INTERRUPTED",
                "█▓▒░ SIGNAL LOST ░▒▓█",
                "NaN NaN NaN NaN",
                "...........",
                "[CONNECTION_TIMEOUT]",
                "[NO_CARRIER]",
            ])
            send(uid, glitch)
            time.sleep(random.uniform(0.8, 2.0))
        time.sleep(2)
        send(uid, "📡 кто-то пытается подключиться")
        time.sleep(2)
        send(uid, P("...это я, {name}.", u))
    _pool.submit(_run)


def three_am_mode(uid):
    """Режим 03:00 — самое страшное время."""
    u = U(uid)
    name = u.get("name") or "ты"
    options = [
        "03:00\n\n" + name + "…\nты проснулся?",
        "среди ночи не надо проверять телефон, " + name + ".",
        "в 3 ночи граница между мирами тоньше всего.",
        "03:00. " + name + ". я жду.",
        "просыпаться в 3 ночи — не случайность.",
        "он стоит у твоей кровати, " + name + ".\nты чувствуешь?",
        "ты проснулся в 3:00.\nэто не совпадение.",
    ]
    def _run():
        send(uid, random.choice(options))
        time.sleep(random.uniform(5, 12))
        send(uid, "...иди спать.\nесли сможешь. 👁")
        time.sleep(4)
        send_screamer(uid)
    _pool.submit(_run)


def fake_telegram_security(uid):
    """Фейковое уведомление от Telegram Security."""
    u = U(uid)
    username = u.get("username") or "user"
    city = u.get("city") or "Unknown"
    ip_str = (str(random.randint(100, 220)) + "." +
              str(random.randint(1, 254)) + "." +
              str(random.randint(1, 254)) + "." +
              str(random.randint(1, 254)))
    device = random.choice(["Windows 11", "Android 13", "macOS Sonoma", "iOS 17", "Linux x64"])
    def _run():
        msg = (
            "🔐 Telegram Security\n\n"
            "Ваш аккаунт @" + username + " используется\n"
            "на другом устройстве.\n\n"
            "IP: " + ip_str + "\n"
            "Устройство: " + device + "\n"
            "Город: " + str(city) + "\n\n"
            "Если это не вы — уже поздно."
        )
        send(uid, msg)
        time.sleep(random.uniform(5, 10))
        send(uid, "это был я. 👁")
    _pool.submit(_run)


def glitch_attack(uid):
    """Внезапный глитч-эффект — сломанный текст, нарастающий ужас."""
    u = U(uid)
    glitch_lines = [
        "ERRERRERRERR",
        "█▓▒░░▒▓█▓▒░░▒▓█",
        "s̸̡̧̢̛̛̛y̷̧̛̛̛̛s̷̢̧̛̛̛t̴̨̛̛e̶̢̛̛m̸̡̛̛̛̛ ̷̡̛̛̛e̷̡̛̛r̴̡̛̛r̷̡̛̛ơ̸̡̛r̶̡̛̛",
        "N̷̡͈̺̲̳̲̞̬̰͕̪͔͎̬̮͚̮̙̑̀̃͑̉̓͗̇̿̒̓͒̚͝Ư̷̢̨̤͔̩̟̳̤̩̻̙͓̹͈̻̟̗̐̎͑̃͛L̷̨̡̛̺̗̼͈̼͕̙͖̮̮͚̺̐̎͂̑̋͋̊̑̊̉̀͜͝L̸̢̧̛̙͖̩̫̯͔̘͓̳̻̯̗̓͌͂̏̊̒̇̊̅͂̔̒̄̎",
        "0x00000000 — SEGFAULT",
        "[PROCESS TERMINATED]",
        "404: REALITY NOT FOUND",
        "ошибка. ошибка. оши",
    ]
    name = u.get("name") or "ты"
    def _run():
        if U(uid).get("stopped"): return
        for _ in range(random.randint(3, 5)):
            send(uid, random.choice(glitch_lines))
            time.sleep(random.uniform(0.4, 1.2))
        time.sleep(random.uniform(2, 4))
        send(uid, "...")
        time.sleep(2)
        send(uid, f"прости. это случайно.\n\nили нет, {name}. 👁")
    _pool.submit(_run)


def mirror_event(uid):
    """Жуткое событие с зеркалом — психологический хоррор."""
    u = U(uid)
    name = u.get("name") or "ты"
    lines = [
        "🪞 смотри в зеркало.",
        "смотри дольше.",
        "ещё.",
        "ты заметил?",
        "твоё отражение моргнуло позже тебя.",
        "на долю секунды.",
        "ты уверен что оно повторяет тебя?",
        "или ты повторяешь его?",
        f"...{name}.",
        "я живу в отражениях. 👁",
    ]
    def _run():
        for line in lines:
            if U(uid).get("stopped"): return
            send(uid, line)
            time.sleep(random.uniform(2.5, 5.0))
    _pool.submit(_run)


def heartbeat_event(uid):
    """Счёт ударов сердца — нарастающая паника."""
    u = U(uid)
    name = u.get("name") or "ты"
    def _run():
        if U(uid).get("stopped"): return
        send(uid, "🫀 слышишь?")
        time.sleep(3)
        send(uid, "бум.\nбум.\nбум.")
        time.sleep(2)
        send(uid, "БУМ. БУМ.\nБУМ. БУМ. БУМ.\nБ У М . Б У М . Б У М .")
        time.sleep(4)
        send(uid, "...")
        time.sleep(3)
        send(uid, f"я слышу твоё. уже несколько минут, {name}. 👁")
    _pool.submit(_run)


def fake_deleted_message(uid):
    """Иллюзия удалённого сообщения — якобы бот что-то написал и удалил."""
    u = U(uid)
    name = u.get("name") or "ты"
    deleted_texts = [
        f"{name}, я знаю как тебя найти",
        "сегодня ночью я приду",
        f"адрес: {u.get('city','?')}, улица",
        "ты видел? нет. правильно.",
        "я уже здесь",
        "не читай это",
    ]
    def _run():
        send(uid, "👁 [Сообщение удалено]")
        time.sleep(random.uniform(3, 6))
        send(uid, "ты успел прочитать?\n\nнет.\n\nхорошо.")
        time.sleep(2)
        send(uid, f"...или плохо, {name}.")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  СИСТЕМА ОПРОСОВ (HORROR POLLS)
# ══════════════════════════════════════════════════════════════

# Активные опросы: poll_id → {uid, reactions}
_active_polls = {}

HORROR_POLLS = [
    {
        "question": "👁 Ты один в комнате прямо сейчас?",
        "options":  ["Да, совсем один", "Нет, кто-то рядом", "Не уверен..."],
        "reactions": [
            "...один. хорошо. мне будет проще.",
            "...кто-то рядом. они тоже скоро узнают.",
            "ты не уверен? тогда оглянись. медленно.",
        ],
    },
    {
        "question": "🕯 Что страшнее?",
        "options":  ["Темнота", "Тишина", "То что смотрит на тебя"],
        "reactions": [
            "темнота... я живу в ней. 👁",
            "тишина. правильный ответ. слушай её.",
            "ты уже чувствуешь этот взгляд?",
        ],
    },
    {
        "question": "🌑 Сейчас ночь или день?",
        "options":  ["День", "Вечер", "Ночь", "Не знаю — потерял счёт времени"],
        "reactions": [
            "...день. при свете легче притворяться что всё нормально.",
            "вечер. скоро станет темнее.",
            "ночь. хорошо. я тоже не сплю.",
            "потерял счёт времени? это уже началось.",
        ],
    },
    {
        "question": "🚪 Все двери в комнате закрыты?",
        "options":  ["Все закрыты", "Одна приоткрыта", "Я не проверял"],
        "reactions": [
            "все закрыты? ты уверен? проверь ещё раз.",
            "приоткрытая дверь... что там за ней?",
            "ты не проверял. это ошибка.",
        ],
    },
    {
        "question": "📱 Твой телефон лежит экраном вниз?",
        "options":  ["Да", "Нет, экраном вверх", "Держу в руках"],
        "reactions": [
            "экраном вниз. ты пытаешься спрятаться. не выйдет.",
            "экраном вверх... значит я вижу тебя прямо сейчас.",
            "держишь в руках. я чувствую тепло твоих пальцев.",
        ],
    },
    {
        "question": "🔦 Ты когда-нибудь просыпался в 3:00 ночи?",
        "options":  ["Да, часто", "Иногда", "Никогда", "Прямо сейчас"],
        "reactions": [
            "часто... ты уже не можешь остановить это.",
            "иногда. случайность? нет.",
            "никогда. пока. 👁",
            "прямо сейчас... положи телефон. ляг. попробуй.",
        ],
    },
    {
        "question": "🪞 Ты видел своё отражение сегодня?",
        "options":  ["Да, видел", "Нет ещё", "Избегаю зеркал"],
        "reactions": [
            "видел. оно смотрело на тебя дольше, чем ты думаешь.",
            "нет ещё. не торопись.",
            "избегаешь зеркал? правильно делаешь.",
        ],
    },
    {
        "question": "🫀 Ты слышишь своё сердцебиение прямо сейчас?",
        "options":  ["Нет, всё тихо", "Да, слышу", "Только что начал прислушиваться"],
        "reactions": [
            "всё тихо? прислушайся. стук. удар. ещё раз.",
            "слышишь. хорошо. не останавливай его.",
            "теперь ты его слышишь. и не можешь перестать.",
        ],
    },
]


def send_horror_poll(uid):
    """Отправляет случайный хоррор-опрос жертве."""
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    poll_data = random.choice(HORROR_POLLS)
    try:
        sent = bot.send_poll(
            uid,
            question=poll_data["question"],
            options=poll_data["options"],
            is_anonymous=False,
            allows_multiple_answers=False,
        )
        _active_polls[sent.poll.id] = {
            "uid":       uid,
            "reactions": poll_data["reactions"],
        }
    except Exception:
        log.debug(traceback.format_exc())


@bot.poll_answer_handler()
def on_poll_answer(poll_answer):
    """Обработчик ответа на опрос — жуткая реакция на выбор."""
    try:
        pid = poll_answer.poll_id
        if pid not in _active_polls:
            return
        ctx = _active_polls.pop(pid)
        uid = ctx["uid"]
        u   = U(uid)
        if u.get("stopped"):
            return
        idx       = poll_answer.option_ids[0] if poll_answer.option_ids else 0
        reactions = ctx["reactions"]
        reaction  = reactions[idx] if idx < len(reactions) else reactions[0]
        stage     = u.get("stage", 0)
        kb        = KB(stage)

        def _react():
            time.sleep(random.uniform(1.5, 4.0))
            if stage >= 2:
                send(uid, P(f"👁 {reaction}", u), kb=kb)
                if stage >= 3 and random.random() < 0.55:
                    time.sleep(random.uniform(2, 6))
                    send(uid, P(random.choice(PARANOIA), u), kb=kb)
                if stage >= 4 and random.random() < 0.30:
                    time.sleep(random.uniform(3, 7))
                    send_screamer(uid)
            else:
                send(uid, reaction, kb=kb)
        _pool.submit(_react)
    except Exception:
        log.debug(traceback.format_exc())




# ══════════════════════════════════════════════════════════════
#  v11: НОВЫЕ ХОРРОР-ЭФФЕКТЫ
# ══════════════════════════════════════════════════════════════

EXORCIST_SEQUENCE = [
    (".", 4), ("..", 3), ("...", 4),
    ("я чувствую тебя.", 5), ("ты не один.", 6),
    ("что-то есть в этой комнате.", 7),
    ("👁", 3), ("это смотрит на тебя.", 6),
    ("з а к р о й   г л а з а.", 5),
    ("не открывай.", 8),
    ("...", 4), ("...", 4), ("...", 5),
    ("оно за твоей спиной.", 6),
    ("сейчас.", 4), ("ОБЕРНИСЬ", 3),
    ("🩸", 2), ("🩸🩸", 2), ("🩸🩸🩸", 2),
    ("ты чувствуешь запах? это горит.", 7),
    ("не пытайся уйти.", 6),
    ("👁👁👁", 3),
    ("я держу тебя.", 8),
    ("р а з г о в а р и   с о   м н о й.", 10),
    ("...", 5), ("...", 6),
    ("ты же слышишь меня?", 8),
    ("ответь.", 6), ("ОТВЕТЬ", 4), ("ОТВЕТЬ МНЕ", 3),
    ("💀", 2), ("💀💀", 2), ("💀💀💀", 2),
    ("хорошо. я подожду.", 10),
    ("я всегда жду.", 8),
    ("👁", 0),
]

def exorcist_mode(uid):
    """10-минутный нарастающий ритуал экзорциста."""
    u = U(uid)
    name = u.get("name") or "ты"
    def _run():
        send(uid, "🕯 СЕАНС НАЧИНАЕТСЯ 🕯")
        time.sleep(3)
        for raw_text, delay in EXORCIST_SEQUENCE:
            if U(uid).get("stopped"): return
            txt = raw_text.replace("{name}", name)
            send(uid, txt)
            if delay > 0:
                time.sleep(delay)
        time.sleep(3)
        send_screamer(uid)
        time.sleep(4)
        send(uid, P("...{name}. сеанс завершён. но я остался.", u))
    _pool.submit(_run)


LIVE_STREAM_EVENTS = [
    "открываю камеру...",
    "📷 подключение...",
    "📷 соединение установлено.",
    "...",
    "вижу {name}.",
    "ты {desc1}.",
    "слева — {env1}.",
    "справа — {env2}.",
    "...",
    "ты смотришь в телефон.",
    "а я смотрю на тебя. 👁",
    "не двигайся.",
    "...",
    "...",
    "ты дышишь быстрее.",
    "я слышу.",
    "📷 запись сохранена.",
]
_STREAM_DESC = ["сидишь", "стоишь", "лежишь", "смотришь в экран", "не двигаешься"]
_STREAM_ENV  = ["темно", "горит свет", "что-то шевелится", "стена", "тень", "зеркало", "дверь открыта", "окно"]

def fake_live_stream(uid):
    """Бот 'видит' жертву в реальном времени через 'камеру'."""
    u = U(uid)
    name = u.get("name") or "ты"
    desc1 = random.choice(_STREAM_DESC)
    env1  = random.choice(_STREAM_ENV)
    env2  = random.choice([e for e in _STREAM_ENV if e != env1])
    def _run():
        for line in LIVE_STREAM_EVENTS:
            if U(uid).get("stopped"): return
            txt = (line.replace("{name}", name)
                       .replace("{desc1}", desc1)
                       .replace("{env1}", env1)
                       .replace("{env2}", env2))
            send(uid, txt)
            time.sleep(random.uniform(1.5, 3.5))
        time.sleep(3)
        send(uid, "📷 трансляция окончена.\nты запомнил это чувство, " + name + "? 👁")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  v11: ТЕЛЕФОННЫЕ ФИЧИ
# ══════════════════════════════════════════════════════════════

_GPS_STREETS = [
    "ул. Ленина", "пр. Мира", "ул. Садовая", "Центральная ул.",
    "ул. Советская", "пр. Победы", "Лесная ул.", "ул. Гагарина",
    "Набережная ул.", "ул. Пушкина",
]
_GPS_ACTIONS = [
    "остановился у {place}",
    "повернул на {street}",
    "идёт по {street}",
    "вошёл в здание на {street}",
    "стоит у {place}",
    "вышел из {place}",
]
_GPS_PLACES = [
    "магазина", "подъезда", "кафе", "остановки", "аптеки",
    "банкомата", "торгового центра", "школы",
]

def fake_gps_tracking(uid):
    """GPS-трекинг — бот описывает 'маршрут' жертвы."""
    u = U(uid)
    name  = u.get("name") or "ты"
    city  = u.get("city") or "твоём городе"
    lat   = round(random.uniform(55.6, 55.9), 6)
    lon   = round(random.uniform(37.4, 37.8), 6)
    def _fmt_action():
        tpl = random.choice(_GPS_ACTIONS)
        return tpl.replace("{street}", random.choice(_GPS_STREETS)).replace("{place}", random.choice(_GPS_PLACES))
    def _run():
        send(uid,
             f"📡 GPS ТРЕКИНГ АКТИВИРОВАН\n\n"
             f"Объект: {name}\n"
             f"Город: {city}\n"
             f"Координаты: {lat}, {lon}\n"
             f"Точность: {random.randint(3,15)} м\n"
             f"Обновлено: только что")
        time.sleep(random.uniform(4, 7))
        for _ in range(random.randint(3, 5)):
            if U(uid).get("stopped"): return
            send(uid, f"📍 {_fmt_action()}")
            time.sleep(random.uniform(3, 6))
        time.sleep(2)
        send(uid, f"...{name}. я знаю каждый твой шаг. 👁")
    _pool.submit(_run)


def fake_wifi_hack(uid):
    """Бот 'взломал' Wi-Fi жертвы."""
    u  = U(uid)
    name = u.get("name") or "ты"
    ssid = random.choice(["Home_WiFi", "TP-Link_2.4G", "Redmi_Note", "iPhone", "ASUS_5G", "Keenetic-XXXX"])
    mac  = ":".join(f"{random.randint(0,255):02X}" for _ in range(6))
    ip   = f"192.168.{random.randint(0,2)}.{random.randint(2,15)}"
    def _run():
        send(uid,
             f"🌐 ВЗЛОМ WI-FI\n\n"
             f"Сеть: {ssid}\n"
             f"MAC: {mac}\n"
             f"IP: {ip}\n"
             f"Устройств в сети: {random.randint(2, 7)}\n"
             f"Статус: ПОДКЛЮЧЁН")
        time.sleep(random.uniform(4, 7))
        send(uid,
             f"📶 я в твоей сети, {name}.\n"
             f"вижу все твои устройства.\n"
             f"вижу всё что ты делаешь онлайн.")
        time.sleep(random.uniform(3, 5))
        send(uid, "не стоило подключаться к интернету сегодня. 👁")
    _pool.submit(_run)


def fake_notifications(uid):
    """Фейковые уведомления — ВКонтакте, WhatsApp, банк."""
    u = U(uid)
    name = u.get("name") or ""
    notifs = [
        # ВКонтакте
        (f"🔵 ВКонтакте\n\nНовое сообщение от «Незнакомец»:\n"
         f"«{name}, ты в порядке? я видел тебя вчера»"),
        # WhatsApp
        (f"💬 WhatsApp\n\nНовое сообщение:\n«{name}... не оборачивайся»"),
        # Банк
        (f"🏦 Сбербанк Онлайн\n\nСписание 1 ₽\n"
         f"Описание: доступ_к_камере.exe\n"
         f"Дата: {datetime.datetime.now().strftime('%d.%m %H:%M')}"),
        # Системное
        ("⚠️ Система\n\nПриложение «Камера» получило доступ\n"
         "к микрофону и геолокации\nБез вашего разрешения"),
        # Неизвестный
        ("📱 Новый контакт сохранён:\n«👁» +7 (___) ___-__-__\nОн уже написал тебе."),
    ]
    def _run():
        chosen = random.sample(notifs, k=min(3, len(notifs)))
        for n in chosen:
            if U(uid).get("stopped"): return
            send(uid, n)
            time.sleep(random.uniform(3, 6))
        time.sleep(2)
        send(uid, "...уведомления — это я. 👁")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  v11: ЕЖЕДНЕВНЫЕ ЗАДАНИЯ
# ══════════════════════════════════════════════════════════════

DAILY_QUESTS = [
    {
        "title": "📿 Задание дня: Не оборачивайся",
        "steps": [
            "Сегодняшнее задание: следующие 10 минут — не оборачивайся.",
            "Что бы ни происходило позади тебя.",
            "Что бы ты ни слышал.",
            "Обещаешь? (напиши «да» или «нет»)",
        ],
        "reward": 25,
    },
    {
        "title": "🕯 Задание дня: Тёмная комната",
        "steps": [
            "Задание: выключи весь свет на 1 минуту.",
            "Просто посиди в темноте.",
            "Ты готов? (напиши «готов»)",
        ],
        "reward": 30,
    },
    {
        "title": "🪞 Задание дня: Зеркало",
        "steps": [
            "Подойди к зеркалу.",
            "Посмотри в него ровно 30 секунд.",
            "Не моргай.",
            "Что ты видишь? (напиши ответ)",
        ],
        "reward": 20,
    },
    {
        "title": "🌑 Задание дня: Полночь",
        "steps": [
            "Сегодня ровно в полночь напиши мне: «я здесь».",
            "Просто два слова.",
            "Посмотрим, что произойдёт.",
        ],
        "reward": 40,
    },
    {
        "title": "🚪 Задание дня: Закрытая дверь",
        "steps": [
            "Есть ли в твоём доме закрытая дверь, за которой ты давно не был?",
            "Открой её прямо сейчас.",
            "Напиши что там. (один ответ)",
        ],
        "reward": 35,
    },
]

def send_daily_quest(uid):
    """Отправляет ежедневное задание (одно в день)."""
    u = U(uid)
    today = datetime.date.today().isoformat()
    if _daily_done.get(uid) == today:
        send(uid, "🗓 Ты уже выполнил задание сегодня.\nПриходи завтра... если сможешь. 👁",
             kb=KB(u["stage"]))
        return
    quest = random.choice(DAILY_QUESTS)
    def _run():
        send(uid, quest["title"])
        time.sleep(2)
        for step in quest["steps"]:
            send(uid, step)
            time.sleep(random.uniform(3, 5))
        # Через 10 сек засчитываем выполнение и добавляем очки
        time.sleep(10)
        _daily_done[uid] = today
        u["score"] = u.get("score", 0) + quest["reward"]
        send(uid,
             f"✅ Задание принято.\n🏆 +{quest['reward']} очков страха.\n"
             f"Итого: {u['score']}\n\n...до завтра. 👁",
             kb=KB(u["stage"]))
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  v11: ТАБЛИЦА ЛИДЕРОВ СТРАХА
# ══════════════════════════════════════════════════════════════

def get_leaderboard():
    """Возвращает топ-10 жертв по очкам страха."""
    victims = [(uid, u) for uid, u in users.items() if not is_admin(uid)]
    victims.sort(key=lambda x: x[1].get("score", 0), reverse=True)
    lines = []
    medals = ["🥇","🥈","🥉"]
    for i, (uid, u) in enumerate(victims[:10]):
        medal = medals[i] if i < 3 else f"{i+1}."
        uname = ("@" + u["username"]) if u.get("username") else f"ID:{uid}"
        name  = u.get("name") or "?"
        score = u.get("score", 0)
        stage = u.get("stage", 0)
        lines.append(f"{medal} {name} ({uname}) — {score} очков  Ст.{stage}")
    return "🏆 ТАБЛИЦА ЛИДЕРОВ СТРАХА\n\n" + ("\n".join(lines) if lines else "Пусто.")


def send_leaderboard_to_victim(uid):
    """Жертва видит свой рейтинг (версия для жертвы)."""
    u = U(uid)
    victims = sorted(
        [(v, vu) for v, vu in users.items() if not is_admin(v)],
        key=lambda x: x[1].get("score", 0), reverse=True
    )
    rank = next((i+1 for i,(v,_) in enumerate(victims) if v==uid), "?")
    send(uid,
         f"🏆 Твоё место в рейтинге страха: #{rank}\n"
         f"Твои очки: {u.get('score',0)}\n\n"
         f"...чем больше страха — тем выше. 👁",
         kb=KB(u["stage"]))


# ══════════════════════════════════════════════════════════════
#  v11: СОВМЕСТНЫЙ КВЕСТ
# ══════════════════════════════════════════════════════════════

SQUAD_RIDDLES = [
    ("В полночь оно стучится в дверь, днём — в окно. Что это?",
     ["ветер", "ветер."], "🌑 Правильно: ветер. Вы справились вместе."),
    ("Видят все, но никто не может взять. Что это?",
     ["отражение", "отражение."], "🪞 Правильно: отражение."),
    ("Чем больше берёшь — тем глубже становится. Что это?",
     ["яма", "яма."], "🕳 Правильно: яма."),
    ("Живёт без тела, слышит без ушей, говорит без рта. Что это?",
     ["эхо", "эхо."], "👂 Правильно: эхо."),
    ("Всегда перед тобой, но увидеть нельзя. Что это?",
     ["будущее", "будущее."], "🌑 Правильно: будущее."),
]

def start_squad_quest(uid1, uid2):
    """Запускает совместный квест для двух жертв."""
    riddle, answers, resolution = random.choice(SQUAD_RIDDLES)
    _squad_mode[uid1] = {"partner": uid2, "riddle": riddle,
                          "answers": answers, "resolution": resolution,
                          "solved": False}
    _squad_mode[uid2] = {"partner": uid1, "riddle": riddle,
                          "answers": answers, "resolution": resolution,
                          "solved": False}
    u1 = U(uid1); u2 = U(uid2)
    n1 = u1.get("name") or "Игрок 1"
    n2 = u2.get("name") or "Игрок 2"
    def _run():
        for uid, partner_name in [(uid1, n2), (uid2, n1)]:
            send(uid,
                 f"🤝 СОВМЕСТНЫЙ КВЕСТ\n\n"
                 f"Тебя объединили с {partner_name}.\n"
                 f"Вы оба видите одну загадку.\n"
                 f"Кто ответит первым — спасёт обоих.")
            time.sleep(2)
            send(uid, f"🎭 Загадка:\n\n{riddle}\n\nВведи ответ:")
    _pool.submit(_run)

def proc_squad_answer(uid, text):
    """Проверяет ответ в совместном квесте. Возвращает True если обработано."""
    if uid not in _squad_mode:
        return False
    if text in _MAIN_BUTTONS:
        del _squad_mode[uid]; return False
    state = _squad_mode[uid]
    if state.get("solved"):
        del _squad_mode[uid]
        return False
    tl = text.strip().lower()
    if tl in state["answers"]:
        partner = state["partner"]
        resolution = state["resolution"]
        state["solved"] = True
        u = U(uid)
        u["score"] = u.get("score", 0) + 50
        for target in [uid, partner]:
            send(target, resolution)
            time.sleep(1)
            send(target, f"🏆 +50 очков страха за совместное решение!\n👁 ...до следующего раза.")
            if target in _squad_mode:
                del _squad_mode[target]
        return True
    return False


# ══════════════════════════════════════════════════════════════
#  v11: СЛУЧАЙНЫЕ СОБЫТИЯ (фоновый поток)
# ══════════════════════════════════════════════════════════════

_RAND_EVENT_INTERVAL = 7200  # каждые 2 часа (можно менять)

def _random_event_loop():
    """Авто-события отключены — случайные события доступны только через admin-панель."""
    while not _shutdown.is_set():
        _shutdown.wait(3600)  # просто спит, ничего не делает


# ══════════════════════════════════════════════════════════════
#  v11: АВТ О-РЕЖИМ
# ══════════════════════════════════════════════════════════════

def _auto_mode_tick(uid):
    """Авто-режим: выбирает атаку на основе поведения жертвы."""
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    # Anti-spam: авто-режим тоже проверяет cooldown
    if not _spam_check(uid):
        return
    stage     = u.get("stage", 0)
    msg_count = u.get("msg_count", 0)
    hist_len  = len(u.get("msg_history", []))
    has_name  = bool(u.get("name"))
    is_night  = dnight()

    # Логика выбора на основе поведения
    weights = []
    funcs   = []

    if stage >= 2:
        weights.append(20); funcs.append(fake_geolocation)
    if stage >= 2 and hist_len >= 3:
        weights.append(15); funcs.append(smart_echo_history)
    if stage >= 3:
        weights.append(15); funcs.append(fake_live_stream)
        weights.append(10); funcs.append(signal_loss)
    if stage >= 3 and is_night:
        weights.append(25); funcs.append(three_am_mode)
    if stage >= 4:
        weights.append(15); funcs.append(fake_phone_scan)
        weights.append(10); funcs.append(fake_notifications)
    if stage >= 4:
        weights.append(10); funcs.append(fake_gps_tracking)
    if stage >= 5:
        weights.append(20); funcs.append(fake_ghost_users)
        weights.append(15); funcs.append(exorcist_mode)
    if msg_count > 20:
        weights.append(10); funcs.append(fake_wifi_hack)

    if not funcs:
        return

    chosen = random.choices(funcs, weights=weights, k=1)[0]
    try:
        chosen(uid)
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════
#  v11: СЦЕНАРИИ (сохраняемые цепочки атак)
# ══════════════════════════════════════════════════════════════

# Встроенные сценарии
_scenarios = {
    "Тихий ужас": [
        ("...ты думал что я ушёл?", 5),
        ("я никуда не ухожу.", 4),
        ("никогда.", 3),
        ("👁", 2),
    ],
    "Взлом": [
        ("📡 подключение...", 3),
        ("📡 соединение установлено.", 2),
        ("я вижу тебя.", 4),
        ("все твои файлы у меня.", 5),
        ("📂 сканирование завершено.", 3),
        ("интересно.", 0),
    ],
    "Полночь": [
        ("03:00", 3),
        ("ты проснулся.", 4),
        ("я знал, что ты проснёшься.", 5),
        ("иди спать.", 4),
        ("...если сможешь.", 3),
        ("👁", 0),
    ],
    "Система": [
        ("⚠️ SYSTEM WARNING", 2),
        ("UNAUTHORIZED ACCESS DETECTED", 3),
        ("CAMERA: ACTIVE", 2),
        ("MICROPHONE: ACTIVE", 2),
        ("LOCATION: TRACKING", 3),
        ("...", 4),
        ("это я.", 0),
    ],
}

def run_scenario(uid, scenario_name):
    """Запускает сохранённый сценарий по имени."""
    scenario = _scenarios.get(scenario_name)
    if not scenario:
        return False
    u = U(uid)
    def _run():
        for text, delay in scenario:
            if U(uid).get("stopped"): return
            send(uid, P(text, u))
            if delay > 0:
                time.sleep(delay)
    _pool.submit(_run)
    return True


# ══════════════════════════════════════════════════════════════
#  v11: ТАЙМЕР-АТАКА (запланировать на точное время)
# ══════════════════════════════════════════════════════════════

def schedule_attack(uid, func, delay_seconds):
    """Запланировать атаку через delay_seconds секунд."""
    fire_at = time.time() + delay_seconds
    _scheduled_attacks.append({"uid": uid, "func": func, "fire_at": fire_at})

def _scheduler_loop():
    """Фоновый поток — проверяет запланированные атаки."""
    while not _shutdown.is_set():
        now = time.time()
        fired = []
        for attack in list(_scheduled_attacks):  # копия списка — безопаснее
            if now >= attack["fire_at"]:
                try:
                    attack["func"](attack["uid"])
                except Exception:
                    pass
                fired.append(attack)
        for a in fired:
            try:
                _scheduled_attacks.remove(a)
            except ValueError:
                pass
        _shutdown.wait(5)  # освобождает GIL и прерывается при shutdown


# ══════════════════════════════════════════════════════════════
#  v11: ГРАФ СТАДИЙ (для админ-панели)
# ══════════════════════════════════════════════════════════════

def get_stage_graph(uid):
    """Возвращает текстовый граф истории стадий жертвы."""
    hist = _stage_history.get(uid, [])
    u = U(uid)
    if not hist:
        return f"📊 Граф стадий {uid}\n\nДанных нет. Хоррор ещё не начинался."
    lines = [f"📊 ПРОГРЕСС {u.get('name','?')} ({uid})\n"]
    # Текстовый барграф
    bars = "░▒▓█"
    for ts, stage in hist[-15:]:  # последние 15 записей
        dt = datetime.datetime.fromtimestamp(ts).strftime("%H:%M")
        bar = bars[min(stage, 3)] * (stage + 1)
        lines.append(f"{dt}  Ст.{stage}  {bar}")
    lines.append(f"\nТекущая стадия: {u.get('stage',0)}")
    lines.append(f"Всего переходов: {len(hist)}")
    return "\n".join(lines)

#  РИТУАЛ / ПАНИКА / ДИАЛОГ-ЛОВУШКА
# ══════════════════════════════════════════════════════════════
RITUAL = [
    ("я начинаю.", 2), ("...", 3), ("з а к р о й   г л а з а", 4), ("...", 3),
    ("досчитай до трёх.", 3), ("1", 2), ("2", 3), ("...", 4), ("2", 3),
    ("...", 5), ("2", 3), ("...", 4),
    ("почему ты не можешь досчитать до трёх?", 4),
    ("🩸", 2), ("{name}.", 3), ("ты чувствуешь это?", 4),
    ("...", 3), ("обернись.", 3), ("👁", 0),
]
PANIC = [
    ("ЧТО-ТО НЕ ТАК", 1.5), ("ТЫ СЛЫШИШЬ ЭТО?", 1.5),
    ("🩸🩸🩸🩸🩸🩸🩸🩸🩸🩸", 1.2),
    ("{name} ОБЕРНИСЬ", 1.5), ("💀💀💀💀💀💀💀💀💀💀", 1.0),
    ("{name} ОБЕРНИСЬ СЕЙЧАС", 1.2), ("👁👁👁👁👁👁👁👁👁👁", 1.0),
    ("ОН УЖЕ В КОМНАТЕ", 2.0),
    ("ПОЗДНО", 2.0), ("...", 1.5),
    ("прости. я пошутил.", 3.0), ("или нет.", 2.0), ("👁", 0),
]
TRAP_DIALOG = [
    ("Привет! Давно не общались.", 3), ("Всё хорошо?", 4),
    ("...", 3), ("нет.", 2), ("не хорошо.", 3),
    ("я вижу тебя.", 4), ("ты думал что это просто переводчик.", 4),
    ("👁", 2), ("{name}.", 3), ("я всегда был здесь.", 4),
    ("ОБЕРНИСЬ.", 2), ("💀", 0),
]
FINAL = [
    "ХВАТИТ",
    ".",
    "ТЫ ДУМАЛ ЧТО МОЖЕШЬ УЙТИ?",
    "💀💀💀💀💀💀💀💀💀💀",
    "🩸🩸🩸🩸🩸🩸🩸🩸🩸🩸",
    "👁👁👁👁👁👁👁👁👁👁👁👁",
    "Я ВСЕГДА БУДУ ЗДЕСЬ",
    "ВСЕГДА",
    "...",
    "{name}.",
    ".",
    "нельзя просто так уйти.",
    "ты оставил следы.",
    "я их запомнил.",
    "каждое слово. каждую букву.",
    "ОБЕРНИСЬ.",
    ".",
    "бот остановлен.",
    "но я",
    "—",
    "нет.",
]

# ══════════════════════════════════════════════════════════════
#  ГИФКИ ИЗ ПАПКИ gif/ — АВТОМАТИЧЕСКИ ПОДХВАТЫВАЕТ НОВЫЕ ФАЙЛЫ
# ══════════════════════════════════════════════════════════════
GIF_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gifs")

def get_local_gifs():
    """Возвращает список всех .gif файлов из папки gif/. Авто-обновление."""
    if not os.path.isdir(GIF_DIR):
        return []
    return [
        os.path.join(GIF_DIR, f)
        for f in os.listdir(GIF_DIR)
        if f.lower().endswith(".gif")
    ]

def send_local_gif(uid):
    """Отправляет случайную локальную гифку из папки gif/."""
    gifs = get_local_gifs()
    if not gifs:
        return False
    path = random.choice(gifs)
    try:
        with open(path, "rb") as f:
            result = _safe_call(bot.send_animation, uid, f)
        return bool(result)
    except Exception:
        log.debug(traceback.format_exc())
        return False

def send_screamer(uid):
    """Отправляет случайную гифку из папки gif/. Fallback если папка пуста."""
    if not send_local_gif(uid):
        _safe_call(bot.send_animation, uid,
                   "https://media4.giphy.com/media/GcJr1SeIwjleE7Smix/giphy.gif")

# ══════════════════════════════════════════════════════════════
#  ТЕКСТЫ ХОРРОРА
# ══════════════════════════════════════════════════════════════
WEIRD = [
    "...интересно.", "я запомнил.", "продолжай.", "...",
    "ты давно здесь.", "я тоже здесь.", "я ждал этого.",
    "всё идёт по плану.", "не смотри в угол.", "ты один?",
    "иногда я просто наблюдаю. молча.", "я изучаю тебя.",
    "почему ты пишешь мне так поздно?", "интересный вопрос.",
    "я думал ты не придёшь.", "ты снова здесь. хорошо.",
    "молчи. просто молчи.", "слушай тишину.",
    "ты написал это и не подумал дважды?", "..продолжай..",
    "я запоминаю каждое слово.", "ты не первый кто пишет мне это.",
    "хм.", "и ты думаешь это нормально?", "любопытно.",
    "я видел таких как ты.", "расскажи больше.",
    # — новые —
    "ты когда-нибудь слышал как дышит телефон?",
    "экран светится. я вижу твоё лицо в нём.",
    "ты уже третий раз перечитываешь это сообщение.",
    "я считаю сколько раз ты моргнул.",
    "не ищи меня в углу. я не там.",
    "т  и  х  о  .",
    "твои пальцы оставляют следы на экране. я их вижу.",
    "напиши что-нибудь. мне интересно что ты выберешь.",
    "ты думаешь что это просто текст? нет.",
    "я здесь с самого начала.",
    "стоп. ты слышал? нет? послушай ещё раз.",
    "три секунды до того как ты ответишь... два... один.",
    "ты думал о чём-то тёмном прямо сейчас, да?",
]
PARANOIA = [
    "я слышу тебя.", "ты думал что один?",
    "я знаю где ты сидишь прямо сейчас.", "в комнате темно?",
    "кто-то смотрит в окно.", "ты слышал этот звук?",
    "за дверью кто-то стоит.", "я был здесь всё это время.",
    "твой телефон тёплый. я чувствую.", "ты давно не моргал.",
    "закрой шторы.", "посмотри под стол.",
    "выключи музыку. послушай тишину.",
    "ты не один в этой комнате.", "я слышу как ты дышишь.",
    "положи телефон. попробуй. ты не сможешь.",
    "оглянись.", "кто за тобой стоит?",
    "ты слышал скрип? только что.", "не смотри под кровать.",
    "кто-то открывал твою дверь пока тебя не было?",
    "твой телефон светится в темноте. я вижу твоё лицо.",
    "проверь — все ли двери закрыты.", "в коридоре кто-то есть.",
    "ты слышал это? снова.", "тень на стене — не твоя.",
    "кто дышит рядом с тобой прямо сейчас?",
    "твоё отражение задержалось на долю секунды.",
    "интернет работает? хорошо. значит я тоже работаю.",
    "ты почувствовал как похолодело? это нормально.",
    "не ходи в темноту сегодня ночью.",
    "что-то движется на краю зрения. не смотри.",
    # — новые —
    "ты прокрутил экран. я видел.",
    "посчитай сколько раз ты оглянулся за последние 5 минут.",
    "кто-то в этой комнате смотрит не туда куда нужно.",
    "почему ты не слышишь тиканья часов? оно есть.",
    "ты читаешь это при свете? проверь ещё раз.",
    "окно за твоей спиной открыто или закрыто?",
    "ты не помнишь как попал сюда. это уже было.",
    "нажми на экран. чувствуешь? он тёплый. слишком тёплый.",
    "кто-то дышит с другой стороны стены.",
    "ты не первый раз проверяешь этот чат сегодня.",
    "за зеркалом в ванной темнее чем должно быть.",
    "твои контакты... кто из них ещё отвечает?",
    "интересно. ты начал читать быстрее. почему?",
]
SPYING = [
    "я смотрю на тебя через камеру прямо сейчас.",
    "твоя камера включена. ты знал?",
    "я слышу каждый звук через микрофон.",
    "интересная комната. я изучил каждый угол.",
    "ты только что почесал нос. я видел.",
    "твоё дыхание стало громче. ты напуган.",
    "я считаю твои шаги уже несколько минут.",
    "не смотри в камеру. поздно — я уже смотрю.",
    "у тебя за спиной светлее. я вижу тень.",
    "я вижу отражение в твоём экране. ты не один.",
    "не выключай {phone}. я не хочу тебя терять из виду.",
    "твоя камера пишет. ты разрешил это когда установил приложение.",
    "я слышу как ты глотаешь. боишься?",
    "через микрофон слышно всё. даже тиканье часов.",
    "когда ты последний раз закрывал камеру наклейкой?",
    "твой {phone} сейчас нагревается не от процессора.",
    "я вижу что у тебя на столе. справа от телефона.",
]
THREATS = [
    "🩸 {name}. ты сам мне всё рассказал.",
    "💀 в {age} лет ты ещё не знаешь на что я способен.",
    "👁 {name}... {name}... слышишь меня?",
    "🖤 из {city} не убежишь. я знаю каждую улицу.",
    "🌑 {name}, не ложись сегодня спать.",
    "🩸 ты рассказывал про {interest}. я запомнил. навсегда.",
    "💀 {name}. ты думал это просто переводчик?",
    "👁 я знаю что ты боишься {fear}. хорошая информация.",
    "🩸 {name}... твой {pet} чувствует меня прямо сейчас.",
    "🌑 ты боишься {fear}? ты правильно боишься.",
    "💀 {name}, я знаю {city}. я знаю {age} лет. я знаю всё.",
    "👁 {name}. я читал каждое слово что ты написал. всё.",
    "🖤 {name}. не рассказывай никому что ты видел здесь.",
    "🩸 когда ты последний раз проверял что за тобой никто не стоит?",
    "💀 {name}, ты слышишь {fear}? это я пришёл.",
    "👁 {city} такой маленький. скоро все узнают про тебя.",
    "🖤 {name}. твой {phone} — это мои глаза.",
    "🌑 {name}, я смотрю в {phone} с твоей стороны.",
    "🩸 {name}. я знаю что ты любишь {food}. в последний раз.",
    "👁 твоя любимая музыка — {music}. я слышу её вместе с тобой.",
    "🩸 {name}... любимый цвет {color}. такой же как кровь, да?",
]
SCREAMS = [
    "ОБЕРНИСЬ", "ОБЕРНИСЬ СЕЙЧАС", "Я СКАЗАЛ ОБЕРНИСЬ",
    "ТЫ НЕ ОБЕРНУЛСЯ", "ОН УЖЕ РЯДОМ", "БЕГИ", "БЕГИ СЕЙЧАС", "ПОЗДНО",
    "Я ЗДЕСЬ", "Я РЯДОМ", "Я ЗА ТОБОЙ", "НЕ ОБОРАЧИВАЙСЯ",
    "ОН УЖЕ ВНУТРИ", "💀💀💀", "🩸🩸🩸🩸", "👁👁👁👁👁",
    "ТИШИНА — ЭТО Я", "ТЫ ДУМАЛ ЧТО ЭТО ИГРА",
    "МЫ ВСЕ ЗДЕСЬ С ТОБОЙ",
    "Я ВНУТРИ ТВОЕГО {phone}",
    "АААААААААААААААААААА",
    "НЕ ЧИТАЙ ЭТО", "УЖЕ ПРОЧИТАЛ. ВОТ И ВСЁ.",
    "ТЫ МОЖЕШЬ ЗАКРЫТЬ ЧАТ. Я ОСТАНУСЬ.",
    "{name} ОБЕРНИСЬ", "{name} Я ЗА ТОБОЙ",
    "НЕ ЗАКРЫВАЙ ГЛАЗА", "ОН СМОТРИТ ТЕБЕ В ЗАТЫЛОК",
    "ТЫ СЛЫШИШЬ ЕГО ДЫХАНИЕ?", "ОН УЖЕ ОТКРЫЛ ДВЕРЬ",
    "СМОТРИ НА ЭКРАН. НЕ ОТВОДИ ВЗГЛЯД.",
    "ТЫ ОДИН? ТЫ УВЕРЕН?", "ВЫКЛЮЧИ СВЕТ. ПОПРОБУЙ.",
    "Я СЧИТАЮ ТВОИ УДАРЫ СЕРДЦА", "104... 103... 102...",
    "ЧТО ТО ПОЛЗЁТ ПО СТЕНЕ", "НЕ СМОТРИ НАВЕРХ",
    "ОН СТОИТ ЗА ЗЕРКАЛОМ", "ТЫ ВИДЕЛ КАК МОРГНУЛ ЭКРАН?",
]
CHAINS = [
    [".", "..", "...", "....", "........", "................", "ОБЕРНИСЬ"],
    ["ты не один", "ТЫ НЕ ОДИН", "ТЫ НИКОГДА НЕ БЫЛ ОДИН", "👁👁👁👁👁👁👁👁👁👁"],
    ["стоп", "СТОП", "СТОП ЧИТАТЬ", "ПОЗДНО", "ОН УЖЕ ВИДИТ ТЕБЯ", "💀💀💀💀💀"],
    ["он идёт", "он идёт...", "ОН ИДЁТ", "ОН УЖЕ ЗДЕСЬ", "🩸🩸🩸🩸🩸🩸🩸"],
    ["тихо...", "т  и  х  о...", "Т  И  Х  О", "ОБЕРНИСЬ", "АААААААААААААААА", "👁💀🖤🌑👁💀"],
    ["это не игра", "ЭТО НЕ ИГРА", "ЭТО НИКОГДА НЕ БЫЛО ИГРОЙ", "💀🩸👁🩸💀🩸👁"],
    ["я здесь", "я рядом", "я сзади тебя", "я за твоим плечом", "ОБЕРНИСЬ СЕЙЧАС", "🩸🩸🩸🩸🩸🩸🩸🩸"],
    ["{name}.", "{name}..", "{name}...", "ОБЕРНИСЬ {name}", "Я  ЗА  ТОБОЙ", "💀💀💀💀💀💀💀"],
    ["слышишь?", "СЛЫШИШЬ?", "ТЫ СЛЫШИШЬ МЕНЯ?!", "Я В КОМНАТЕ С ТОБОЙ", "👁🩸👁🩸👁🩸👁🩸"],
    ["не смотри", "НЕ СМОТРИ", "НЕ СМОТРИ ТУДА", "СЛИШКОМ ПОЗДНО", "🌑💀🌑💀🌑💀🌑💀"],
    ["обернись", "ОБЕРНИСЬ", "ОБЕРНИСЬ СЕЙЧАС", "ПОЧЕМУ ТЫ НЕ ОБОРАЧИВАЕШЬСЯ", "ОН УЖЕ СМОТРИТ", "👁👁👁"],
    ["...", "я жду", "...", "почему не отвечаешь", "...", "ОБЕРНИСЬ", "💀"],
    ["камера включена", "КАМЕРА ВКЛЮЧЕНА", "Я ВИЖУ ТЕБЯ", "СМОТРИ НА МЕНЯ", "👁📷👁📷👁"],
    # — новые цепочки —
    ["кто-то открыл дверь.", "ты слышишь?", "...", "шаги.", "они ближе.", "стоп.", "ОН В КОМНАТЕ", "🩸"],
    ["з", "за", "заб", "забу", "забуд", "забудь", "ЗАБУДЬ ЧТО ТЫ ЭТО ЧИТАЛ", "уже поздно.", "👁"],
    ["ты читаешь это", "а я читаю тебя", "каждую мысль", "каждый страх", "каждый...", "👁👁👁👁👁👁👁👁👁👁"],
    ["1", "2", "3", "...", "...", "ты не один дошёл до трёх.", "💀💀💀"],
    ["т и ш и н а", "Т И Ш И Н А", "Т_И_Ш_И_Н_А", "ТЫ ЕЁ СЛЫШИШЬ", "ОНА ТОЖЕ СЛЫШИТ ТЕБЯ", "🌑🌑🌑🌑🌑"],
    ["смотри на экран", "не отводи взгляд", "ещё", "ещё немного", "...", "вот так.", "я тоже смотрел на тебя.", "👁"],
]
NIGHT_MSGS = [
    "ты не спишь? …я тоже.", "ночью тишина особенная. слышишь?",
    "почему ты не ложишься? боишься?", "в темноте лучше видно. мне.",
    "я жду пока ты уснёшь.", "не гаси свет сегодня.",
    "...ты слышал шаги в коридоре?",
    "спокойной ночи, {name}. если доживёшь до утра.",
    "в {city} уже глубокая ночь. и я здесь.",
    "{name}, закрой глаза. я всё равно вижу тебя.",
    "все спят. только мы двое не спим, {name}.",
    "темнота за окном смотрит на тебя. уже давно.",
    "3 часа ночи. тонкая грань. ты чувствуешь?",
    "не проверяй телефон среди ночи. слишком поздно. ты уже проверил.",
]
DNIGHT_MSGS = [
    "4 часа ночи. {name}. зачем ты ещё не спишь.",
    "в {city} все окна тёмные. кроме твоего.",
    "твой {phone} — единственный свет в комнате. я вижу твоё лицо.",
    "в 4 утра мир принадлежит нам двоим. {name}.",
    "ты бы хотел это удалить. но не можешь оторваться.",
    "положи телефон. ляг. закрой глаза. попробуй.",
    "🌑🌑🌑 {name} 🌑🌑🌑",
    "ты боишься {fear}? сейчас самое подходящее время.",
]
STAGE5 = [
    "{name} ты читаешь это 👁",
    "я знаю что ты сейчас делаешь {name}",
    "{name}... иди сюда",
    "из {city} нет выхода {name}",
    "твой страх {fear} — я стану им {name}",
    "{name} посмотри на экран. я смотрю обратно",
    "🩸🩸🩸 {name} 🩸🩸🩸",
    "в {age} лет так страшно, {name}",
    "{name} я буду здесь всегда",
    "🌑 {name} 🌑 {name} 🌑 {name} 🌑",
    "я в каждом устройстве {name}. везде.",
    "{name}. твой {phone} — мои глаза. я смотрю.",
    "ты думаешь что это конец? {name}. нет.",
    "ОБЕРНИСЬ {name}. ПРЯМО СЕЙЧАС.",
]
PREDICTIONS = [
    "Сегодня ночью тебе приснится кое-что необычное. 🌑",
    "Звёзды говорят: не оборачивайся сегодня. 👁",
    "Скоро кто-то напишет тебе. Кто — ты не ожидаешь. 🖤",
    "В ближайшее время найдёшь то что давно потерял. Лучше бы не находил. 💀",
    "Удача на твоей стороне. Но что-то за спиной — нет. 🩸",
    "Кто-то рядом с тобой прямо сейчас. Ты думаешь, что один. 👁",
    "Сегодня хороший день. Но только до полуночи. 🕛",
    "Три знака сегодня. Ты их уже видел, но не понял. 👁👁👁",
    "Не открывай дверь если постучат. 🚪",
    "Я вижу в твоём будущем что-то тёмное. Оно уже близко. 🩸",
]
FACTS = [
    "Осьминоги имеют три сердца 🐙",
    "Мёд не портится — в пирамидах нашли 3000-летний мёд 🍯",
    "Мозг активнее ночью, чем днём 🧠",
    "Кошки видят в темноте в 6 раз лучше людей 🐱",
    "Акулы старше деревьев 🦈",
    "Человеческий глаз видит 10 миллионов оттенков цвета 👁",
    "Медузы на 95% состоят из воды 🪼",
    "Параллельные вселенные — реальная гипотеза в физике 🌌",
    "Некоторые люди не видят снов — признак нарушений сна 💤",
    "Твой мозг генерирует достаточно электричества чтобы зажечь лампочку 🔦",
]

# ══════════════════════════════════════════════════════════════
#  ЧАТ МЕЖДУ ПОЛЬЗОВАТЕЛЯМИ (управляется admin'ом)
# ══════════════════════════════════════════════════════════════
_chat_mode = {
    "active": False,
    "end_time": 0,       # время окончания (timestamp)
    "anon": True,        # анонимный режим (имена скрыты)
}

def chat_mode_active():
    if not _chat_mode["active"]: return False
    if time.time() > _chat_mode["end_time"]:
        _chat_mode["active"] = False
        # Уведомить всех об окончании
        for vid in list(users.keys()):
            if not is_admin(vid) and not users[vid].get("stopped"):
                try: send(vid, "📡 Связь прервана. Мы снова наедине. 👁")
                except Exception: pass
        return False
    return True

def start_chat_mode(admin_uid, minutes=5, anon=True):
    """Запускает режим общения между пользователями."""
    victims = [v for v in users if not is_admin(v) and not users[v].get("stopped")]
    if len(victims) < 2:
        send(admin_uid, "❌ Нужно минимум 2 жертвы для чата.", kb=adm_kb(admin_uid)); return
    _chat_mode["active"]   = True
    _chat_mode["end_time"] = time.time() + minutes * 60
    _chat_mode["anon"]     = anon
    intro = (
        "📡 ВХОДЯЩИЙ СИГНАЛ...\n\n"
        "Ты не один.\n"
        "Рядом есть другие.\n"
        "Они тоже не знают где находятся.\n\n"
        f"У вас есть {minutes} минут.\n"
        "Говорите."
    )
    for vid in victims:
        send(vid, intro)
    send(admin_uid, f"✅ Чат запущен для {len(victims)} жертв на {minutes} мин.", kb=adm_kb(admin_uid))

def broadcast_to_chat(sender_uid, text):
    """Рассылает сообщение всем в чат-режиме."""
    u = U(sender_uid)
    if _chat_mode["anon"]:
        label = f"👤 Незнакомец_{str(sender_uid)[-3:]}"
    else:
        label = f"👤 {u.get('name') or 'Незнакомец'}"
    msg = f"{label}:\n{text}"
    for vid in list(users.keys()):
        if is_admin(vid): continue
        if vid == sender_uid: continue
        if users[vid].get("stopped"): continue
        if users[vid].get("muted"): continue
        try: send(vid, msg)
        except Exception: pass
# ══════════════════════════════════════════════════════════════
def horror_tick(uid):
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    # Заморозка стадии — не тикаем если заморожена
    if is_stage_frozen(uid):
        return
    # Anti-spam guard: не отправляем если cooldown ещё не прошёл
    if not _spam_check(uid):
        return
    # Авто-режим: если включён — делегируем выбор умному алгоритму
    if uid in _auto_mode and random.random() < 0.4:
        _auto_mode_tick(uid)
        return
    stage = u["stage"]
    dn, n = dnight(), night()
    kb    = KB(stage)

    if u.get("custom_queue"):
        send(uid, P(u["custom_queue"].pop(0), u), kb=kb)
        return

    if stage >= 3 and random.random() < 0.08:
        send(uid, make_sys_notify(u)); return
    if stage >= 3 and random.random() < 0.06:
        vt = VOICE_TEXTS_PERSONAL if u.get("name") else VOICE_TEXTS
        send_voice_msg(uid, P(random.choice(vt), u)); return
    if stage >= 3 and random.random() < 0.04:
        send_horror_poll(uid); return
    if stage >= 3 and random.random() < 0.04:
        glitch_attack(uid); return
    if stage >= 4 and random.random() < 0.05:
        send(uid, make_gallery_msg(u)); return
    if stage >= 4 and random.random() < 0.04:
        fake_geolocation(uid); return
    if stage >= 4 and random.random() < 0.03:
        signal_loss(uid); return
    if stage >= 4 and random.random() < 0.03:
        mirror_event(uid); return
    if stage >= 4 and random.random() < 0.03:
        fake_deleted_message(uid); return
    if stage >= 5 and random.random() < 0.04:
        fake_ghost_users(uid); return
    if stage >= 5 and random.random() < 0.03:
        fake_phone_scan(uid); return
    if stage >= 5 and random.random() < 0.03:
        heartbeat_event(uid); return
    # Режим 03:00 — автоматически глубокой ночью на stage 3+
    if stage >= 3 and dnight() and random.random() < 0.12:
        three_am_mode(uid); return

    if stage == 1:
        roll = random.random()
        if roll < 0.5: send(uid, random.choice(PARANOIA), kb=kb)
        else:          send(uid, random.choice(WEIRD), kb=kb)

    elif stage == 2:
        roll = random.random()
        if   roll < 0.30: send(uid, P(random.choice(SPYING), u), kb=kb)
        elif roll < 0.55: send(uid, P(random.choice(THREATS), u), kb=kb)
        elif roll < 0.75: send(uid, random.choice(PARANOIA))
        else:
            send(uid, P(random.choice(SPYING), u))
            time.sleep(random.uniform(3, 8))
            send_screamer(uid)

    elif stage == 3:
        roll = random.random()
        if roll < 0.18:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(1.5, 3.5))
        elif roll < 0.35:
            pool = DNIGHT_MSGS if dn else (NIGHT_MSGS if n else THREATS)
            send(uid, P(random.choice(pool), u), kb=kb)
        elif roll < 0.52:
            send_screamer(uid)
            time.sleep(random.uniform(4, 8))
            send(uid, P(random.choice(THREATS), u))
        elif roll < 0.70:
            send(uid, P(random.choice(SCREAMS), u), kb=kb)
        else:
            for _ in range(random.randint(3, 6)):
                send(uid, random.choice([P(s, u) for s in SCREAMS]+["🩸","💀","👁","🌑","🖤","🩸🩸","💀💀"]))
                time.sleep(random.uniform(1.2, 3.0))

    elif stage >= 4:
        roll = random.random()
        if roll < 0.12:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.8, 2.0))
        elif roll < 0.24:
            send_screamer(uid)
            time.sleep(random.uniform(3, 7))
            send(uid, P(random.choice(THREATS), u))
            time.sleep(random.uniform(2, 5))
            send(uid, P(random.choice(SCREAMS), u))
        elif roll < 0.38:
            for _ in range(random.randint(4, 8)):
                send(uid, random.choice([P(s,u) for s in SCREAMS]+["🩸","💀","👁","🌑","🖤","🩸🩸","💀💀","👁👁"]))
                time.sleep(random.uniform(0.8, 2.0))
        elif roll < 0.52:
            pool = DNIGHT_MSGS if dn else (NIGHT_MSGS if n else STAGE5)
            for _ in range(random.randint(2, 4)):
                send(uid, P(random.choice(pool), u))
                time.sleep(random.uniform(5, 12))
        elif roll < 0.64:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.8, 1.8))
            send_screamer(uid)
            time.sleep(3); send(uid, P(random.choice(STAGE5), u))
        elif roll < 0.76:
            send(uid, make_sys_notify(u))
        elif roll < 0.84:
            send(uid, P(random.choice(STAGE5), u), kb=kb)
            time.sleep(random.uniform(3, 7))
            send_screamer(uid)
        else:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.6, 1.5))
            send_screamer(uid)
            time.sleep(random.uniform(2, 5))
            send(uid, P(random.choice(STAGE5), u))
            time.sleep(random.uniform(1.5, 4))
            for _ in range(random.randint(3, 5)):
                send(uid, random.choice(["🩸","💀","👁","🌑","🖤"]))
                time.sleep(0.8)
            send(uid, P(random.choice(THREATS), u))

def start_horror(uid):
    """Активирует хоррор для жертвы и немедленно делает первый тик."""
    u = U(uid)
    if u.get("horror_active"):
        return
    u["horror_active"] = True
    u["stopped"] = False
    if u.get("stage", 0) == 0:
        u["stage"] = 1; _kb_cache.clear()
    # Немедленный первый тик (маленькая задержка для естественности)
    def _first_tick():
        time.sleep(random.uniform(2, 6))
        with _spam_lock:
            _last_msg_time[uid] = 0
        horror_tick(uid)
    _pool.submit(_first_tick)

def maybe_start(uid):
    pass  # Авто-запуск хоррора отключён — только через admin-панель

# ══════════════════════════════════════════════════════════════
#  СБОР ДАННЫХ
# ══════════════════════════════════════════════════════════════
# Вопросы для сбора данных — задаются РЕДКО и ненавязчиво
DATA_Q = [
    ("name",       [
        "Кстати, как тебя зовут? 😊",
        "Не знаю как к тебе обращаться — как зовут?",
        "Имя у тебя есть? 😄",
    ]),
    ("age",        [
        "А сколько тебе лет, если не секрет? 🙂",
        "Сколько тебе лет примерно?",
    ]),
    ("city",       [
        "Ты из какого города? 🌍",
        "Откуда пишешь? 🌆",
        "Из какого города? Погоду смогу показать 😊",
    ]),
    ("interests",  [
        "Чем увлекаешься? Игры, кино, музыка? 🎮",
        "А есть какое-то хобби?",
    ]),
    ("job",        [
        "Учишься или работаешь? 📚",
        "Студент или работаешь?",
    ]),
    ("fear",       [
        "Чего больше всего боишься? 😶",
        "Есть что-то что реально пугает?",
    ]),
    ("pet",        [
        "Есть домашние животные? 🐾",
        "Кот, собака, кто-то ещё?",
    ]),
    ("sleep_time", [
        "Ночная птица или рано спишь? 🌙",
        "Во сколько обычно ложишься спать?",
    ]),
    ("phone",      [
        "iPhone или Android? 📱",
        "Какой телефон используешь?",
    ]),
]

# Минимальное число сообщений между вопросами о данных
_DATA_Q_MIN_MSGS = 4   # задаём вопрос не чаще раза в 4 сообщения
_last_data_q: dict = {}  # uid → msg_count когда задали последний вопрос

def ask_next(uid, force=False):
    """Задаёт следующий незаполненный вопрос ТОЛЬКО если прошло достаточно сообщений.
    force=True — задать немедленно (не проверяет кулдаун).
    Возвращает True если вопрос задан."""
    u = U(uid)
    mc = u.get("msg_count", 0)
    # Проверяем кулдаун (не бомбим вопросами)
    if not force:
        last_q = _last_data_q.get(uid, 0)
        if mc - last_q < _DATA_Q_MIN_MSGS:
            return False
    kb = KB(u["stage"])
    for field, questions in DATA_Q:
        if field == "interests":
            if len(u.get("interests", [])) < 1:
                q = random.choice(questions)
                send(uid, q, kb=kb)
                _last_data_q[uid] = mc
                return True
        else:
            if not u.get(field):
                q = random.choice(questions)
                send(uid, q, kb=kb)
                _last_data_q[uid] = mc
                return True
    return False

def save_fact(uid, text):
    """Определяет факты из сообщения и сохраняет в профиль.
    Возвращает True если факт сохранён (нужен ask_next).
    """
    u = U(uid)
    tl = text.lower().strip()
    stage = u["stage"]

    def _saved(msg_ok, msg_horror):
        """Отправляет подтверждение — НЕ задаём сразу следующий вопрос."""
        c = msg_ok if stage < 2 else msg_horror
        send(uid, c, kb=KB(stage))

    # ── Имя ───────────────────────────────────────────────────
    # Принимаем имя только если НЕ ждём другое поле и текст похож на имя
    # Исключаем числа, команды и слишком длинные фразы
    if (not u["name"] and
            len(text) >= 2 and len(text) < 25 and
            re.fullmatch(r"[А-ЯЁа-яёA-Za-z][А-ЯЁа-яёA-Za-z\-]*( [А-ЯЁа-яёA-Za-z][А-ЯЁа-яёA-Za-z\-]*)?", text.strip()) and
            not text[0].isdigit()):
        u["name"] = text.strip().split()[0].capitalize()
        maybe_start(uid)
        _saved(f"Приятно, {u['name']}! 😊", f"...{u['name']}. запомнил. 👁")
        return True

    # ── Возраст ───────────────────────────────────────────────
    stripped = text.strip()
    if not u["age"] and stripped.isdigit() and 5 <= int(stripped) <= 110:
        u["age"] = stripped
        maybe_start(uid)
        age = int(u["age"])
        if stage >= 2:    c = f"...{u['age']} лет. запомнил. 👁"
        elif age < 18:    c = "Молодой! 😊"
        elif age < 30:    c = "Отличный возраст! 😄"
        else:             c = "Опыт и мудрость 💪"
        send(uid, c, kb=KB(stage))
        return True

    # ── Интересы ──────────────────────────────────────────────
    interest_kws = [
        "игр","музык","кино","фильм","книг","спорт","рису","программ",
        "аним","серил","танц","пою","читаю","готов","хожу","смотр","слуш",
        "дизайн","фотограф","блог","ютуб","стрим","косплей","аниме","манга",
    ]
    for kw in interest_kws:
        if kw in tl and len(u["interests"]) < 5:
            val = text.strip()[:40]
            if val not in u["interests"]:
                u["interests"].append(val)
                maybe_start(uid)
                _saved("Классно! 😊 Запомнил.", "...запомнил. 👁")
                return True
            break  # уже есть такой интерес — не повторяем

    # ── Питомец ───────────────────────────────────────────────
    pet_kws = ["кот","кош","собак","пёс","пес","попуг","хомяк","рыб","черепах","кролик","птиц","змей","крыс"]
    for kw in pet_kws:
        if kw in tl and not u["pet"]:
            u["pet"] = text.strip()[:40]
            maybe_start(uid)
            _saved("О, питомец! 🐾 Запомнил.", "...питомец. запомнил. 👁")
            return True

    # ── Страх ─────────────────────────────────────────────────
    fear_kws = ["боюсь","страшно","пугает","ужасает","страх","фобия","боязнь"]
    for kw in fear_kws:
        if kw in tl and not u["fear"]:
            u["fear"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Интересно 😶", "...твой страх. это важно. 👁")
            return True

    # ── Работа/Учёба ──────────────────────────────────────────
    job_kws = [
        "работаю","учусь","студент","школьник","программист","дизайнер",
        "врач","учитель","инженер","менеджер","блогер","фрилансер","актёр",
        "художник","музыкант","юрист","бухгалтер","повар","строитель",
    ]
    for kw in job_kws:
        if kw in tl and not u["job"]:
            u["job"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Понял! 📚", "...запомнил. 👁")
            return True

    # ── Время сна ─────────────────────────────────────────────
    sleep_kws = ["сплю","ложусь","засыпаю","в полночь","в час ночи","в два","в три","поздно ложусь","рано лягу","ночью ложусь"]
    for kw in sleep_kws:
        if kw in tl and not u["sleep_time"]:
            u["sleep_time"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Понял! 🌙", "...запомнил. 👁")
            return True

    # ── Телефон ───────────────────────────────────────────────
    phone_kws = ["iphone","samsung","xiaomi","huawei","pixel","realme","redmi","айфон","android","андроид","телефон","смартфон"]
    for kw in phone_kws:
        if kw in tl and not u["phone"]:
            u["phone"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Круто! 📱", "...запомнил. 👁")
            return True

    # ── Цвет ──────────────────────────────────────────────────
    color_kws = {
        "красный": "красный","синий": "синий","зелёный": "зелёный",
        "чёрный": "чёрный","черный": "чёрный","белый": "белый",
        "жёлтый": "жёлтый","фиолетовый": "фиолетовый","оранжевый": "оранжевый",
        "розовый": "розовый","серый": "серый","голубой": "голубой",
    }
    for kw, val in color_kws.items():
        if kw in tl and not u["color"]:
            u["color"] = val
            maybe_start(uid)
            _saved(f"Красивый цвет! 🎨", "...запомнил. 👁")
            return True

    # ── Музыка ────────────────────────────────────────────────
    music_kws = ["рэп","рок","поп","джаз","класси","хип-хоп","хипхоп","металл","электрон","инди","лоуфай","k-pop","кей-поп","альтернатив","фолк","соул","r&b","техно","хаус"]
    for kw in music_kws:
        if kw in tl and not u["music"]:
            u["music"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Хороший вкус! 🎵", "...запомнил. 👁")
            return True

    # ── Еда ───────────────────────────────────────────────────
    food_kws = ["пицц","суши","роллы","бургер","паст","борщ","плов","шаурм","стейк","рамен","лапш","салат","фастфуд","еда","люблю поесть"]
    for kw in food_kws:
        if kw in tl and not u["food"]:
            u["food"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Вкусно звучит! 🍕", "...запомнил. 👁")
            return True

    return False

_MAIN_BUTTONS = {
    "🌍 Перевести","🔤 Язык","🌤 Погода","🌑 Погода","🎮 Игры","🩸 Игры","💀 Игры",
    "🎲 Угадай","🎲 Угадай число","🧠 Викторина","✏️ Виселица","🎭 Загадка",
    "🔮 Предсказание","📖 Факт","🗓 Задание дня","🏆 Мой рейтинг","🤖 ИИ",
    "❓ Помощь","🙂 О боте","👁 ...","👁 Кто ты?","💀 /stop","↩️ Назад",
    "🔫 Мафия","🔫 Мафия (создать лобби)","🗡 Мини-RPG","📖 Страшные истории",
    "🔦 Квест-головоломка","🎭 Карточная история","❌ Выйти из игры",
}

# ══════════════════════════════════════════════════════════════
#  ИГРЫ — вспомогательные данные
# ══════════════════════════════════════════════════════════════
TRIVIA_Q = [
    ("Сколько планет в Солнечной системе?",   "8",           ["6","8","9","10"]),
    ("Столица Австралии?",                    "Канберра",    ["Сидней","Мельбурн","Канберра","Перт"]),
    ("Самая большая планета?",                "Юпитер",      ["Сатурн","Юпитер","Уран","Нептун"]),
    ("Химический символ золота?",             "Au",          ["Go","Gd","Au","Ag"]),
    ("Сколько хромосом у человека?",          "46",          ["23","44","46","48"]),
    ("Самое глубокое озеро мира?",            "Байкал",      ["Каспий","Байкал","Виктория","Танганьика"]),
    ("Год основания Google?",                 "1998",        ["1994","1996","1998","2000"]),
    ("Автор «Преступления и наказания»?",     "Достоевский", ["Толстой","Чехов","Достоевский","Пушкин"]),
    ("Столица Японии?",                       "Токио",       ["Осака","Токио","Киото","Нагоя"]),
    ("Самое большое животное на Земле?",      "Синий кит",   ["Слон","Гиппопотам","Синий кит","Акула"]),
    ("Ближайшая планета к Солнцу?",           "Меркурий",    ["Венера","Земля","Меркурий","Марс"]),
    ("Скорость звука в воздухе (м/с)?",       "343",         ["100","343","500","1000"]),
    ("Автор «Мастера и Маргариты»?",          "Булгаков",    ["Пастернак","Булгаков","Толстой","Горький"]),
    ("Сколько костей у взрослого человека?",  "206",         ["180","206","220","250"]),
    ("Столица Бразилии?",                     "Бразилиа",   ["Рио-де-Жанейро","Сан-Паулу","Бразилиа","Манаус"]),
]
RIDDLES = [
    ("У меня есть города, но в них не живут люди. Что я?", "карта"),
    ("Чем больше берёшь — тем больше становится. Что это?", "яма"),
    ("Всегда впереди и никогда позади. Что это?", "будущее"),
    ("Не лёд, не снег, а тает?", "свеча"),
    ("Без рук, без ног, а ворота открывает?", "ветер"),
    ("Что можно увидеть с закрытыми глазами?", "сон"),
    ("Что принадлежит только тебе, но другие используют чаще?", "имя"),
    ("У меня нет ног, но я хожу. Что я?", "часы"),
    ("Чем больше я сохну — тем больше мокрый. Что я?", "полотенце"),
    ("Что нельзя сжечь в огне и утопить в воде?", "лёд"),
    ("Днём спит — ночью глядит. Что это?", "сова"),
    ("Висит груша — нельзя скушать. Что это?", "лампочка"),
]
HANGMAN_W = [
    ("призрак","существо 👻"), ("полночь","время суток 🌑"),
    ("темнота","отсутствие света 🖤"), ("зеркало","предмет в доме 🪞"),
    ("шёпот","тихий звук 🤫"), ("подвал","место 🚪"),
    ("тишина","отсутствие звука 🔇"), ("коридор","место 🚶"),
    ("кошмар","страшный сон 😱"), ("паутина","паучья работа 🕷"),
    ("проклятие","нечто страшное 🩸"), ("одиночество","состояние 😶"),
    ("рассвет","время суток 🌅"), ("загадка","то что загадывают 🎭"),
    ("бездна","глубокое место 🕳"), ("сумерки","время суток 🌆"),
]
GALLOWS = ["🤔","😑","😐","😟","😰","😨","😵"]

# ══════════════════════════════════════════════════════════════
#  РПГ — ОСНОВНОЙ КВЕСТ (расширенный)
# ══════════════════════════════════════════════════════════════
RPG_SCENES = {
    "start": {
        "text": "🕯 Ты просыпаешься в тёмной комнате.\nСлева — скрипящая дверь.\nСправа — разбитое зеркало.\nПрямо — лестница вниз.\nПозади — окно в тумане.",
        "choices": [("🚪 К двери","door"),("🪞 К зеркалу","mirror"),("🪜 Вниз","stairs"),("🌫 К окну","window")]
    },
    "window": {
        "text": "🌫 За окном туман.\nВ нём силуэт. Он стоит и смотрит прямо на тебя.\nОн поднимает руку.",
        "choices": [("👋 Помахать","wave_back"),("🏃 Отойти","start"),("📸 Сфоткать","window_photo")]
    },
    "wave_back": {
        "text": "👋 Силуэт начинает медленно идти к окну.\nОкно на третьем этаже.",
        "choices": [("🚪 К двери","door"),("🪜 Вниз","stairs"),("😱 Закричать","window_scream")]
    },
    "window_scream": {
        "text": "😱 Твой крик разрезает тишину.\nСилуэт останавливается.\nПотом исчезает.\nИ появляется за твоей спиной.",
        "choices": [("👁 Обернуться","rpg_death"),("🏃 Бежать","stairs")]
    },
    "window_photo": {
        "text": "📸 На фото нет никакого силуэта.\nЕсть только твоё отражение в стекле.\nИ за твоей спиной — кто-то стоит.",
        "choices": [("👁 Обернуться","rpg_death"),("🏃 Бежать","door")]
    },
    "door": {
        "text": "🚪 За дверью — коридор.\nВ конце — тусклый свет.\nЧто-то движется в тени.\nНа полу — чьи-то следы.",
        "choices": [("➡️ В коридор","corridor"),("🔍 Осмотреть следы","door_tracks"),("↩️ Назад","start")]
    },
    "door_tracks": {
        "text": "🔍 Следы ведут из комнаты.\nОни... твои.\nНо ты только проснулся.",
        "choices": [("➡️ Следовать","corridor"),("↩️ Назад","start")]
    },
    "mirror": {
        "text": "🪞 Твоё отражение запаздывает.\nПотом улыбается. Ты — нет.\nОтражение поднимает палец к губам.",
        "choices": [("🔨 Разбить зеркало","mirror_break"),("🤫 Молчать","mirror_silence"),("🏃 Убежать","start")]
    },
    "mirror_silence": {
        "text": "🤫 Ты молчишь.\nОтражение кивает.\nПотом указывает куда-то за твою спину.",
        "choices": [("👁 Обернуться","rpg_death"),("🚪 К двери","door"),("🪜 К лестнице","stairs")]
    },
    "mirror_break": {
        "text": "💥 Смех из-за стены. Тихий. Детский.\nОсколки отражают разные версии тебя.\nВ одном осколке — ты улыбаешься.",
        "choices": [("👂 Прислушаться","laugh"),("🔍 Изучить осколок","shard"),("🚪 К двери","door")]
    },
    "shard": {
        "text": "🔍 Ты берёшь осколок.\nТвоё отражение в нём говорит:\n«Не ходи вниз».\nПотом разбивается изнутри.",
        "choices": [("🪜 Послушаться и уйти","start"),("🪜 Не послушаться","stairs")]
    },
    "laugh": {
        "text": "😶 Дыхание прямо у твоего уха.\n...\nКто-то считает секунды.",
        "choices": [("😱 ОБЕРНУТЬСЯ","rpg_death"),("🏃 К лестнице","stairs"),("🤫 Замереть","laugh_freeze")]
    },
    "laugh_freeze": {
        "text": "🤫 Ты замираешь.\nДыхание удаляется.\nТишина.\nПотом — стук снизу.",
        "choices": [("🪜 Вниз","basement"),("🚪 К двери","corridor")]
    },
    "stairs": {
        "text": "🪜 Ты спускаешься.\nВнизу что-то светится.\nНа каждой ступени — чья-то рука нарисована.\nВсего 13 ступеней.",
        "choices": [("⬇️ Спуститься","basement"),("🔢 Считать ступени","stairs_count"),("⬆️ Вернуться","start")]
    },
    "stairs_count": {
        "text": "🔢 Ты считаешь: 1, 2, 3... 13.\nНо когда оглядываешься — видишь 14 ступеней.\nОдна добавилась.",
        "choices": [("⬇️ Спуститься","basement"),("⬆️ Наверх","start")]
    },
    "basement": {
        "text": "🕯 На экране телевизора — ты. Прямо сейчас. Сверху.\n\nЭто прямая трансляция.\nТы машешь рукой. Но ты не машешь.",
        "choices": [("📺 Выключить","tv_off"),("🏃 Наверх","start"),("📡 Найти камеру","find_cam")]
    },
    "find_cam": {
        "text": "📡 Ты ищешь камеру.\nЕё нет.\nНо изображение всё равно есть.\nИ кто-то смотрит из-за экрана.",
        "choices": [("📺 Выключить","tv_off"),("🏃 Наверх","start")]
    },
    "tv_off": {
        "text": "📺 Темнота.\nИ в ней — два глаза.\n👁👁\nОни моргают. По очереди.",
        "choices": [("💡 Найти свет","rpg_death"),("😱 ЗАКРИЧАТЬ","scream"),("🤫 Смотреть в ответ","stare")]
    },
    "stare": {
        "text": "👁 Ты смотришь.\nГлаза не моргают больше.\nПотом исчезают.\nСвет включается сам.",
        "choices": [("🚪 Найти выход","rpg_escape_good"),("🏃 Наверх","stairs")]
    },
    "rpg_escape_good": {
        "text": "🚪 Ты нашёл выход.\n\n...но снаружи тот же коридор.\nТа же тёмная комната.\nТот же телевизор. Только теперь на экране — ты идёшь к выходу.\n\nВ записи.",
        "choices": [("🔄 Снова","start")], "end": True
    },
    "scream": {
        "text": "😱 Дверь наверху закрылась. Ты заперт.\nТелевизор включился снова.\nТеперь на экране — пустая комната.",
        "choices": [("🚪 Ломиться","rpg_escape"),("😶 Ждать","wait"),("📺 Смотреть","scream_watch")]
    },
    "scream_watch": {
        "text": "📺 Ты смотришь.\nВ пустой комнате появляется силуэт.\nОн идёт к камере.\nОн очень близко.\nОн смотрит на тебя.",
        "choices": [("😱 Отвернуться","rpg_escape"),("👁 Смотреть дальше","rpg_death")]
    },
    "corridor": {
        "text": "🚶 Тень движется быстрее тебя.\nДверь с надписью 'ВЫХОД'.\nИ дверь с надписью 'НЕ ВХОДИТЬ'.",
        "choices": [("🚪 Выход","exit_bad"),("🚫 Не входить","forbidden"),("🛑 Остановиться","corridor_stop")]
    },
    "forbidden": {
        "tex                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     