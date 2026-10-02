"""
AutoSMMway — универсальный плагин перепродажи SMM-услуг на FunPay для FunPay Cardinal.

Поставщики (SMMway, любые SMM-панели API v2, произвольные REST API) описываются профилями,
которые создаются и редактируются из Telegram. Все данные плагина (база SQLite, конфиг, бэкапы)
лежат в папке storage/plugins/autosmmway и не зависят от версии файла плагина.
"""
from __future__ import annotations

import base64
import difflib
import hashlib
import hmac
import html
import json
import logging
import os
import random
import re
import secrets as pysecrets
import shutil
import sqlite3
import statistics
import threading
import time
import zipfile
from contextlib import contextmanager
from datetime import datetime
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, InvalidOperation
from typing import TYPE_CHECKING, Any, Callable, Optional

import requests
from FunPayAPI.common.enums import OrderStatuses, SubCategoryTypes, Currency
from FunPayAPI.common import exceptions as fp_exceptions
from FunPayAPI.updater.events import NewOrderEvent, NewMessageEvent, OrderStatusChangedEvent
from telebot.types import InlineKeyboardMarkup as K, InlineKeyboardButton as B, CallbackQuery, Message
from tg_bot import CBT

if TYPE_CHECKING:
    from cardinal import Cardinal


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# A. МЕТАДАННЫЕ И КОНСТАНТЫ
# ═══════════════════════════════════════════════════════════════════════════════════════════════

NAME = "AutoSMMway"
VERSION = "1.3.0"
DESCRIPTION = ("Универсальная перепродажа SMM-услуг: любые поставщики через профили, мастер-лоты, "
               "автозаказы, мульти-поставщик, автоподнятие, перенос лотов.")
CREDITS = "@autosmmway"
UUID = "131b861f-1cb2-4c7d-9923-31409fb14ea3"
SETTINGS_PAGE = True

LOGGER_PREFIX = "[AutoSMMway]"
logger = logging.getLogger("FPC.autosmmway")

SCHEMA_VERSION = 3
EXPORT_FORMAT_VERSION = 1

DATA_DIR = os.path.join("storage", "plugins", "autosmmway")
DB_PATH = os.path.join(DATA_DIR, "autosmmway.db")
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")
SECRET_PATH = os.path.join(DATA_DIR, "secret.key")
BACKUP_DIR = os.path.join(DATA_DIR, "backups")
EXPORT_DIR = os.path.join(DATA_DIR, "exports")
TMP_DIR = os.path.join(DATA_DIR, "tmp")

PAGE_SIZE = 8
CB_PREFIX = "asm"
STATE_INPUT = "asm_input"
STATE_FILE = "asm_file"
USER_AGENT = f"Mozilla/5.0 (compatible; AutoSMMway/{VERSION}; +FunPayCardinal)"

INTERNAL_SUPPLIER_STATUSES = ("PENDING", "IN_PROGRESS", "COMPLETED", "PARTIAL", "CANCELED", "FAILED")

ORDER_NEW = "NEW"
ORDER_WAIT_LINK = "WAIT_LINK"
ORDER_WAIT_CONFIRM = "WAIT_CONFIRM"
ORDER_SENDING = "SENDING"
ORDER_IN_PROGRESS = "IN_PROGRESS"
ORDER_COMPLETED = "COMPLETED"
ORDER_PARTIAL = "PARTIAL"
ORDER_CANCELED = "CANCELED"
ORDER_FAILED = "FAILED"
ORDER_REFUNDED = "REFUNDED"
ORDER_CLOSED = "CLOSED"
ORDER_UNCERTAIN = "UNCERTAIN"
ORDER_REFUND_PENDING = "REFUND_PENDING"
ACTIVE_ORDER_STATUSES = (ORDER_NEW, ORDER_WAIT_LINK, ORDER_WAIT_CONFIRM, ORDER_SENDING, ORDER_IN_PROGRESS,
                         ORDER_UNCERTAIN, ORDER_REFUND_PENDING)
# Статусы, при которых заказ «занимает» ссылку и слот покупателя.
BUSY_ORDER_STATUSES = (ORDER_WAIT_CONFIRM, ORDER_SENDING, ORDER_IN_PROGRESS, ORDER_UNCERTAIN)
FINAL_ORDER_STATUSES = (ORDER_COMPLETED, ORDER_PARTIAL, ORDER_CANCELED, ORDER_FAILED, ORDER_REFUNDED,
                        ORDER_CLOSED)

SELECT_MODES = ("CHEAPEST", "QUALITY", "BALANCED", "FIXED")
PRICE_BASES = ("CHEAPEST", "SELECTED", "WORST")
PRICE_MODES = ("per_1000", "pack", "per_1")

STATUS_EMOJI = {
    ORDER_NEW: "🆕", ORDER_WAIT_LINK: "🔗", ORDER_WAIT_CONFIRM: "❔", ORDER_SENDING: "📤",
    ORDER_IN_PROGRESS: "⏳", ORDER_COMPLETED: "✅", ORDER_PARTIAL: "🌓", ORDER_CANCELED: "🚫",
    ORDER_FAILED: "❌", ORDER_REFUNDED: "💸", ORDER_CLOSED: "📁", ORDER_UNCERTAIN: "❓", ORDER_REFUND_PENDING: "⌛",
}

# Причины автовозврата: код -> (текст покупателю, текст админу)
REFUND_REASONS = {
    "no_balance": ("временно нет возможности выполнить услугу", "недостаточно баланса у всех поставщиков"),
    "no_api": ("услуга временно недоступна", "поставщик не подключён (нет ключа/выключен)"),
    "api_down": ("сервис поставщика временно недоступен", "API поставщиков недоступно"),
    "auth": ("услуга временно недоступна", "ошибка авторизации API (проверьте ключ)"),
    "service": ("услуга временно недоступна у поставщика", "услуга отключена/недоступна у всех поставщиков"),
    "no_supplier": ("услуга временно недоступна", "нет подходящих кандидатов (лимиты min/max, рейтинг)"),
    "all_failed": ("не удалось запустить заказ", "все поставщики отказали"),
    "link": ("ссылка не принимается сервисом (профиль закрыт или неверный)", "поставщик отклонил ссылку"),
    "fx": ("техническая ошибка расчёта", "нет курса валюты"),
    "link_timeout": ("ссылка не была получена вовремя", "покупатель не прислал ссылку"),
    "link_attempts": ("не удалось получить корректную ссылку", "превышено число попыток ввода ссылки"),
    "partial": ("заказ выполнен не полностью", "частичное выполнение, дозаказ остатка не удался"),
    "timeout": ("заказ не выполнен в срок", "превышено максимальное время выполнения"),
    "qty": ("выбранное количество недоступно для этой услуги", "количество вне min/max всех кандидатов"),
    "blacklist": ("заказ не может быть выполнен", "покупатель в чёрном списке"),
    "limit": ("превышен лимит заказов", "лимит заказов покупателя в час"),
    "manual": ("заказ отменён продавцом", "возврат вручную"),
    "uncertain": ("не удалось подтвердить запуск заказа", "неясный результат отправки, таймаут решения"),
}

DEFAULTS: dict[str, Any] = {
    "admin_ids": [],
    "dry_run": True,
    # Комиссии в %: сверяйте с актуальными условиями FunPay и вашего способа вывода.
    "fp_fee": 0.0,
    "withdraw_fee": 0.0,
    "fixed_fee": 0.0,
    "margin_default": 30.0,
    "min_margin": 10.0,
    "rate_buffer": 3.0,
    "round_step": 1.0,
    "min_profit_abs": 5.0,
    "price_basis": "WORST",
    "margins": {"service": {}, "category": {}},
    "select_mode_default": "CHEAPEST",
    "select_mode_by_category": {},
    "w_price": 0.5,
    "w_quality": 0.5,
    "min_rating": 0.3,
    "fx": {"source": "funpay", "interval_min": 60, "manual": {"USD": 95.0, "EUR": 103.0, "RUB": 1.0}},
    "price_check_interval": 15,
    "price_change_threshold": 2.0,
    "respect_manual_edits": True,
    "catalog_ttl": 600,
    "lot_unit": 1000,
    "lot_stock": 9999,
    "desc_marker": True,
    "fp_pause": 1.5,
    "poll_interval": 60,
    "max_wait_hours": 72,
    "confirm_timeout": 30,
    "link_attempts": 3,
    "max_active_per_link": 1,
    "max_active_per_buyer": 3,
    "blacklist_refund": True,
    "status_regex": r"(когда|статус|где|долго|скоро|сколько ждать|when|status)",
    "status_reply_cooldown": 300,
    "default_start_time": "0-1 ч",
    "eta_defaults": {"default": 3600, "просмотр": 1800, "view": 1800, "лайк": 3600, "like": 3600,
                     "подписч": 14400, "follower": 14400, "subscriber": 14400, "member": 14400},
    "raise": {"enabled": False, "categories": [], "night_pause": True, "night_start": "02:00",
              "night_end": "07:00", "jitter_min": 5},
    "digest": {"enabled": True, "time": "09:00"},
    "alerts": {"balance_threshold": 5.0, "price_rise_pct": 10.0, "stuck_hours": 24, "error_series": 5,
               "cooldown_min": 60},
    "loyalty": {"enabled": True, "level1": 3, "level3": 5, "level5": 7},
    "smart_discount": {"enabled": False, "days": 7},
    "badge_top_n": 5,
    "badge_text": "🔥 Топ продаж",
    "backup_keep": 5,
    "circuit_errors": 3,
    "circuit_pause": 600,
    # Автопилот: чем больше включено, тем меньше ручной работы.
    "auto": {
        "refund_on_fail": True,          # автовозврат, если заказ не удалось отправить ни одному поставщику
        "transient_retry_min": 30,       # сколько минут повторять при сетевых сбоях перед возвратом
        "link_timeout_hours": 24,        # возврат, если покупатель не прислал ссылку (0 — выкл)
        "link_attempts_refund": False,   # возврат после исчерпания попыток ввода ссылки
        "confirm_auto_start": True,      # запуск без «+» после напоминания, если ссылка валидна
        "partial_policy": "reorder_then_refund",
        "refund_retry_min": 10,          # повтор неудавшегося возврата через N минут
        "refund_retry_max": 6,
        "uncertain_refund_hours": 0,     # автовозврат «неясных» заказов через N ч (0 — только админ)
        "pause_lots_low_balance": True,  # выключать лоты, когда баланса поставщиков не хватает
        "pause_lots_missing_service": True,
        "auto_alternatives": True,       # автоподбор запасных поставщиков для лотов
        "alt_min_score": 0.72,
        "refill_requests": True,         # покупатель пишет «докрутка» — плагин сам отправляет refill
        "refill_regex": r"(докрут|отписал|списал|упал|пропал|уменьшил|refill|drop)",
        "refill_cooldown_hours": 24,
        "refill_window_days": 30,
        "confirm_reminder_hours": 24,    # напомнить подтвердить заказ (0 — выкл)
        "daily_backup": True,
        "max_orders_per_buyer_hour": 10,
        "notify_new_orders": False,
    },
    "masterlot": {"margin_presets": [15, 20, 25, 30, 40, 50], "title_limit": 100, "desc_limit": 3000,
                  "min_price": 1.0, "skip_unprofitable": True},
    "messages": {
        "accepted": [
            "Здравствуйте, {buyer}! Заказ #{order_id} принят: {service_name}, {quantity} шт.",
            "Спасибо за заказ #{order_id}, {buyer}! Услуга: {service_name}, количество {quantity}.",
            "Заказ #{order_id} получен 👍 {service_name} — {quantity} шт.",
        ],
        "ask_link": [
            "Пришлите, пожалуйста, ссылку для выполнения (https://...). Ссылка должна быть открытой.",
            "Отправьте ссылку на профиль/пост одним сообщением, начиная с https://",
        ],
        "bad_link": [
            "Ссылка не подходит: {status}. Пришлите корректную ссылку (https://, без пробелов).",
            "Не получилось распознать ссылку ({status}). Попробуйте ещё раз.",
        ],
        "link_busy": [
            "По этой ссылке уже выполняется заказ. Дождитесь завершения или пришлите другую ссылку.",
        ],
        "confirm": [
            "Проверьте данные:\nСсылка: {link}\nКоличество: {quantity}\nЕсли всё верно — отправьте «+», "
            "чтобы изменить ссылку — «-».",
            "Заказ #{order_id}: {quantity} шт. на {link}\nПодтвердите «+» или отправьте «-» для замены ссылки.",
        ],
        "confirm_reminder": [
            "Напоминаю: заказ #{order_id} ждёт подтверждения. Отправьте «+», если ссылка {link} верна.",
            "Заказ #{order_id} ещё не запущен — подтвердите данные знаком «+».",
        ],
        "queued_limit": [
            "У вас уже есть активные заказы. Заказ #{order_id} будет запущен после их завершения.",
        ],
        "in_progress": [
            "Заказ #{order_id} запущен ✅ Примерное время выполнения: {eta}.",
            "Запустили заказ #{order_id}. Ожидаемое время: {eta}. Можете спросить «статус» в любой момент.",
            "Заказ #{order_id} в работе, ориентировочно {eta}.",
        ],
        "delayed": [
            "Заказ #{order_id} выполняется чуть дольше обычного. Статус: {status}, осталось {remain}.",
            "Небольшая задержка по заказу #{order_id}: выполнено {progress}. Всё под контролем.",
        ],
        "status": [
            "Заказ #{order_id}: {status}. Выполнено {progress}, осталось {remain}. Ожидание: {eta}.",
            "Статус заказа #{order_id}: {status} ({progress}).",
        ],
        "completed": [
            "Заказ #{order_id} выполнен 🎉 Пожалуйста, подтвердите заказ на FunPay и оставьте отзыв!",
            "Готово! Заказ #{order_id} выполнен. Буду благодарен за подтверждение и отзыв ⭐",
        ],
        "partial": [
            "Заказ #{order_id} выполнен частично: осталось {remain} из {quantity}. Возврат за невыполненную "
            "часть будет оформлен, продавец уже уведомлён.",
            "К сожалению, заказ #{order_id} выполнен не полностью (остаток {remain}). Мы свяжемся по поводу "
            "компенсации.",
        ],
        "canceled": [
            "Заказ #{order_id} не удалось выполнить, средства возвращены. Приносим извинения.",
            "Заказ #{order_id} отменён, деньги возвращены на ваш баланс FunPay.",
        ],
        "promo": [
            "Спасибо, что вы с нами! Ваш промокод {status}: +{progress} к количеству следующего заказа. "
            "Пришлите его в чат после оплаты.",
        ],
        "auto_refund": [
            "Заказ #{order_id}: {status}. Средства автоматически возвращены на ваш баланс FunPay. Приносим извинения!",
            "К сожалению, заказ #{order_id} не может быть выполнен ({status}). Деньги уже возвращены.",
        ],
        "link_reminder": [
            "Напоминаю: для запуска заказа #{order_id} пришлите ссылку (https://...). Без ссылки заказ будет "
            "отменён с возвратом средств.",
        ],
        "auto_started": [
            "Подтверждения не было, запускаю заказ #{order_id} по ссылке {link} ✅",
        ],
        "refill_ok": [
            "Запрос на докрутку по заказу #{order_id} отправлен ✅ Обычно восстановление занимает до 24-72 ч.",
        ],
        "refill_denied": [
            "По заказу #{order_id} докрутка недоступна: {status}.",
        ],
        "confirm_please": [
            "Заказ #{order_id} выполнен. Если всё в порядке — подтвердите, пожалуйста, получение на FunPay и "
            "оставьте отзыв 🙏",
        ],
        "promo_applied": [
            "Промокод применён: к заказу #{order_id} добавлено {progress}.",
        ],
    },
}

MESSAGE_TITLES = {
    "accepted": "Заказ принят", "ask_link": "Запрос ссылки", "bad_link": "Неверная ссылка",
    "link_busy": "Ссылка занята", "confirm": "Подтверждение", "confirm_reminder": "Напоминание",
    "queued_limit": "Лимит заказов", "in_progress": "В работе", "delayed": "Задерживается",
    "status": "Ответ на «статус»", "completed": "Завершён", "partial": "Частично выполнен",
    "canceled": "Отмена/возврат", "promo": "Выдача промокода", "promo_applied": "Промокод применён",
    "auto_refund": "Автовозврат", "link_reminder": "Напоминание о ссылке", "auto_started": "Автозапуск без «+»",
    "refill_ok": "Докрутка отправлена", "refill_denied": "Докрутка недоступна", "confirm_please": "Просьба подтвердить",
}

LOT_CODE_WORDS_HELP = {
    "service_name": "название услуги у поставщика",
    "category": "категория услуги",
    "id": "маркер лота ASM-<поставщик>-<услуга>",
    "supplier": "название поставщика",
    "min": "минимальное количество",
    "max": "максимальное количество",
    "price_per_1k": "цена за 1000 шт. в ₽",
    "quantity": "количество в лоте (пакет или единица)",
    "refill": "есть ли докрутка (да/нет)",
    "cancel": "можно ли отменить (да/нет)",
    "start_time": "время старта (из названия услуги или по умолчанию)",
    "speed": "скорость (из названия услуги)",
    "guarantee": "гарантия (R30 → 30 дней)",
    "badge": "бейдж «Топ продаж» для лидеров недели",
    "platform": "платформа (Instagram, TikTok, ...)",
}
MESSAGE_CODE_WORDS_HELP = {
    "order_id": "номер заказа FunPay", "buyer": "ник покупателя", "service_name": "название услуги",
    "quantity": "количество", "link": "ссылка покупателя", "eta": "ожидаемое время", "status": "статус",
    "remain": "остаток", "progress": "прогресс выполнения",
}


def _log(level: int, text: str) -> None:
    logger.log(level, f"{LOGGER_PREFIX} {text}")


def log_info(text: str) -> None:
    _log(logging.INFO, text)


def log_warn(text: str) -> None:
    _log(logging.WARNING, text)


def log_error(text: str, exc: bool = False) -> None:
    _log(logging.ERROR, text)
    if exc:
        logger.debug("TRACEBACK", exc_info=True)


def mask_secret(value: Any) -> str:
    """Маскирует ключ/секрет для логов."""
    s = str(value or "")
    if len(s) <= 6:
        return "***"
    return f"{s[:3]}***{s[-2:]}"


def mask_link(link: Any) -> str:
    """Маскирует ссылку покупателя для логов."""
    s = str(link or "")
    m = re.match(r"(https?://[^/]+/)(.*)", s)
    if not m:
        return mask_secret(s)
    tail = m.group(2)
    return m.group(1) + (tail[:3] + "***" if tail else "")


def esc(value: Any) -> str:
    return html.escape(str(value if value is not None else ""))


def now_ts() -> int:
    return int(time.time())


def D(value: Any, default: str = "0") -> Decimal:
    """Безопасное приведение к Decimal."""
    if isinstance(value, Decimal):
        return value
    if value is None or value == "":
        return Decimal(default)
    try:
        if isinstance(value, float):
            return Decimal(repr(value))
        return Decimal(str(value).replace(",", ".").replace(" ", ""))
    except (InvalidOperation, ValueError):
        return Decimal(default)


def money(value: Any) -> str:
    d = D(value).quantize(Decimal("0.01"))
    return f"{d:,.2f}".replace(",", " ")


def fmt_ts(ts: Optional[int]) -> str:
    if not ts:
        return "—"
    return datetime.fromtimestamp(int(ts)).strftime("%d.%m %H:%M")


def fmt_duration(seconds: Optional[float]) -> str:
    if seconds is None:
        return "—"
    seconds = int(max(0, seconds))
    if seconds < 60:
        return f"{seconds} с"
    minutes = seconds // 60
    if minutes < 60:
        return f"{minutes} мин"
    hours, minutes = divmod(minutes, 60)
    if hours < 24:
        return f"{hours} ч {minutes} мин" if minutes else f"{hours} ч"
    days, hours = divmod(hours, 24)
    return f"{days} д {hours} ч" if hours else f"{days} д"


def to_bool(value: Any) -> bool:
    """Приводит «1», «true», «yes», «да» и т.п. к bool."""
    if isinstance(value, bool):
        return value
    if value is None:
        return False
    if isinstance(value, (int, float, Decimal)):
        return value != 0
    return str(value).strip().lower() in ("1", "true", "yes", "y", "on", "да", "+")


def to_int(value: Any, default: int = 0) -> int:
    try:
        return int(D(value, str(default)))
    except (InvalidOperation, ValueError, TypeError):
        return default


def norm_text(text: Any) -> str:
    return re.sub(r"\s+", " ", str(text or "")).strip().lower()


def parse_hhmm(value: str, default: str = "00:00") -> tuple[int, int]:
    m = re.match(r"^\s*(\d{1,2}):(\d{2})\s*$", str(value or default))
    if not m:
        m = re.match(r"^\s*(\d{1,2}):(\d{2})\s*$", default)
    h, mi = int(m.group(1)), int(m.group(2))
    return max(0, min(23, h)), max(0, min(59, mi))


def deep_merge(base: dict, override: dict) -> dict:
    result = json.loads(json.dumps(base))
    for k, v in (override or {}).items():
        if isinstance(v, dict) and isinstance(result.get(k), dict):
            result[k] = deep_merge(result[k], v)
        else:
            result[k] = v
    return result


def ensure_dirs() -> None:
    for d in (DATA_DIR, BACKUP_DIR, EXPORT_DIR, TMP_DIR):
        os.makedirs(d, exist_ok=True)


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# B. CONFIG: загрузка/сохранение настроек (JSON), валидация, значения по умолчанию
# ═══════════════════════════════════════════════════════════════════════════════════════════════

# (путь, название, тип, группа). Типы: pct, money, int, float, bool, str, time, choice:<a|b>, ids, regex
SETTINGS_SCHEMA: list[tuple[str, str, str, str]] = [
    ("fp_fee", "Комиссия FunPay, %", "pct", "fees"),
    ("withdraw_fee", "Комиссия вывода, %", "pct", "fees"),
    ("fixed_fee", "Фикс. надбавка, ₽", "money", "fees"),
    ("rate_buffer", "Запас на курс, %", "pct", "fees"),
    ("margin_default", "Маржа по умолчанию, %", "pct", "margin"),
    ("min_margin", "Мин. маржа (умные скидки), %", "pct", "margin"),
    ("min_profit_abs", "Мин. прибыль с заказа, ₽", "money", "margin"),
    ("round_step", "Шаг округления цены, ₽", "money", "margin"),
    ("price_basis", "База цены", "choice:CHEAPEST|SELECTED|WORST", "margin"),
    ("select_mode_default", "Режим выбора поставщика", "choice:CHEAPEST|QUALITY|BALANCED|FIXED", "margin"),
    ("w_price", "Вес цены (BALANCED)", "float", "margin"),
    ("w_quality", "Вес качества (BALANCED)", "float", "margin"),
    ("min_rating", "Мин. рейтинг услуги", "float", "margin"),
    ("smart_discount.enabled", "Умные скидки", "bool", "margin"),
    ("smart_discount.days", "Дней без продаж до скидки", "int", "margin"),
    ("fx.source", "Источник курса", "choice:funpay|cbr|manual", "fx"),
    ("fx.interval_min", "Обновление курса, мин", "int", "fx"),
    ("fx.manual.USD", "Ручной курс USD", "float", "fx"),
    ("fx.manual.EUR", "Ручной курс EUR", "float", "fx"),
    ("price_check_interval", "Проверка цен, мин", "int", "intervals"),
    ("price_change_threshold", "Порог изменения цены, %", "pct", "intervals"),
    ("poll_interval", "Опрос статусов, с", "int", "intervals"),
    ("max_wait_hours", "Макс. ожидание заказа, ч", "int", "intervals"),
    ("confirm_timeout", "Таймаут подтверждения, мин", "int", "intervals"),
    ("catalog_ttl", "TTL каталога, с", "int", "intervals"),
    ("fp_pause", "Пауза между вызовами FP, с", "float", "intervals"),
    ("lot_unit", "Единиц в режиме «за 1000»", "int", "lots"),
    ("lot_stock", "Наличие в лоте", "int", "lots"),
    ("desc_marker", "Маркер {id} в описании", "bool", "lots"),
    ("respect_manual_edits", "Уважать ручные правки", "bool", "lots"),
    ("badge_top_n", "Топ-N для бейджа", "int", "lots"),
    ("badge_text", "Текст бейджа", "str", "lots"),
    ("default_start_time", "Старт по умолчанию", "str", "lots"),
    ("link_attempts", "Попыток ввода ссылки", "int", "abuse"),
    ("max_active_per_link", "Активных заказов на ссылку", "int", "abuse"),
    ("max_active_per_buyer", "Активных заказов на покупателя", "int", "abuse"),
    ("blacklist_refund", "Возврат для ЧС", "bool", "abuse"),
    ("status_regex", "Regex вопросов о статусе", "regex", "abuse"),
    ("status_reply_cooldown", "Пауза ответа о статусе, с", "int", "abuse"),
    ("raise.night_pause", "Ночная пауза поднятия", "bool", "night"),
    ("raise.night_start", "Начало ночи (ЧЧ:ММ)", "time", "night"),
    ("raise.night_end", "Конец ночи (ЧЧ:ММ)", "time", "night"),
    ("raise.jitter_min", "Случайный сдвиг, мин", "int", "night"),
    ("alerts.balance_threshold", "Порог баланса поставщика", "float", "alerts"),
    ("alerts.price_rise_pct", "Алерт роста цены, %", "pct", "alerts"),
    ("alerts.stuck_hours", "Заказ завис через, ч", "int", "alerts"),
    ("alerts.error_series", "Серия ошибок для алерта", "int", "alerts"),
    ("alerts.cooldown_min", "Пауза повторного алерта, мин", "int", "alerts"),
    ("digest.enabled", "Ежедневный дайджест", "bool", "alerts"),
    ("digest.time", "Время дайджеста", "time", "alerts"),
    ("loyalty.enabled", "Лояльность (промокоды)", "bool", "loyalty"),
    ("loyalty.level1", "Бонус после 1-го заказа, %", "int", "loyalty"),
    ("loyalty.level3", "Бонус после 3-го заказа, %", "int", "loyalty"),
    ("loyalty.level5", "Бонус после 5+ заказов, %", "int", "loyalty"),
    ("auto.refund_on_fail", "Автовозврат при ошибке отправки", "bool", "auto"),
    ("auto.transient_retry_min", "Повторять при сбоях сети, мин", "int", "auto"),
    ("auto.link_timeout_hours", "Возврат без ссылки через, ч (0 — выкл)", "int", "auto"),
    ("auto.link_attempts_refund", "Возврат после попыток ввода ссылки", "bool", "auto"),
    ("auto.confirm_auto_start", "Запуск без «+» после напоминания", "bool", "auto"),
    ("auto.partial_policy", "Частичное выполнение",
     "choice:reorder_then_refund|reorder_then_admin|refund|admin", "auto"),
    ("auto.refund_retry_min", "Повтор неудачного возврата, мин", "int", "auto"),
    ("auto.refund_retry_max", "Попыток возврата", "int", "auto"),
    ("auto.uncertain_refund_hours", "Возврат «неясных» через, ч (0 — выкл)", "int", "auto"),
    ("auto.pause_lots_low_balance", "Пауза лотов при нехватке баланса", "bool", "auto"),
    ("auto.pause_lots_missing_service", "Пауза лотов без доступных услуг", "bool", "auto"),
    ("auto.auto_alternatives", "Автоподбор запасных поставщиков", "bool", "auto"),
    ("auto.alt_min_score", "Мин. схожесть для запасного (0-1)", "float", "auto"),
    ("auto.refill_requests", "Автодокрутка по запросу покупателя", "bool", "auto"),
    ("auto.refill_regex", "Regex запроса докрутки", "regex", "auto"),
    ("auto.refill_cooldown_hours", "Пауза между докрутками, ч", "int", "auto"),
    ("auto.refill_window_days", "Окно докрутки, дней", "int", "auto"),
    ("auto.confirm_reminder_hours", "Напомнить подтвердить через, ч", "int", "auto"),
    ("auto.max_orders_per_buyer_hour", "Заказов на покупателя в час", "int", "auto"),
    ("auto.daily_backup", "Ежедневный автобэкап", "bool", "auto"),
    ("auto.notify_new_orders", "Уведомлять о каждом заказе", "bool", "auto"),
    ("masterlot.title_limit", "Лимит длины заголовка", "int", "lots"),
    ("masterlot.min_price", "Мин. цена лота, ₽", "money", "lots"),
    ("masterlot.skip_unprofitable", "Пропускать убыточные лоты", "bool", "lots"),
    ("dry_run", "Dry-run (ничего не отправлять)", "bool", "system"),
    ("admin_ids", "ID админов (через запятую)", "ids", "system"),
    ("backup_keep", "Хранить бэкапов", "int", "system"),
    ("circuit_errors", "Ошибок до паузы поставщика", "int", "system"),
    ("circuit_pause", "Пауза поставщика, с", "int", "system"),
]

SETTINGS_GROUPS = {
    "fees": "💳 Комиссии", "margin": "📈 Маржа и выбор", "fx": "💱 Курс валют", "intervals": "⏱ Интервалы",
    "lots": "🏷 Лоты", "abuse": "🛡 Антиабьюз", "night": "🌙 Ночной режим", "alerts": "🔔 Алерты",
    "loyalty": "🎁 Лояльность", "auto": "🤖 Автопилот", "system": "🧰 Система",
}


class Config:
    """Настройки плагина в JSON с дефолтами из DEFAULTS."""

    def __init__(self, path: str = CONFIG_PATH):
        self.path = path
        self.lock = threading.RLock()
        self.data: dict = json.loads(json.dumps(DEFAULTS))
        self.load()

    def load(self) -> None:
        """Загружает конфиг и дополняет недостающие ключи значениями по умолчанию."""
        with self.lock:
            raw: dict = {}
            if os.path.exists(self.path):
                try:
                    with open(self.path, "r", encoding="utf-8") as f:
                        raw = json.load(f)
                except Exception:
                    log_error("Конфиг повреждён, создаю копию и использую значения по умолчанию.", exc=True)
                    try:
                        shutil.copy(self.path, self.path + f".broken_{now_ts()}")
                    except OSError:
                        pass
            self.data = deep_merge(DEFAULTS, raw)
            self.validate()
            self.save()

    def save(self) -> None:
        """Атомарно сохраняет конфиг."""
        with self.lock:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False, indent=2)
            os.replace(tmp, self.path)

    def validate(self) -> None:
        """Приводит значения к допустимым типам и диапазонам."""
        for key, _title, typ, _group in SETTINGS_SCHEMA:
            value = self.get(key)
            default = self._get_from(DEFAULTS, key)
            try:
                self._set_raw(key, self.coerce(typ, value))
            except ValueError:
                log_warn(f"Некорректное значение настройки {key}={value!r}, используется {default!r}")
                self._set_raw(key, default)
        for key in ("fp_fee", "withdraw_fee"):
            if float(self.data[key]) >= 100:
                self.data[key] = 0.0
        msgs = self.data.get("messages") or {}
        for k, v in DEFAULTS["messages"].items():
            if not isinstance(msgs.get(k), list) or not msgs.get(k):
                msgs[k] = list(v)
        self.data["messages"] = msgs
        if self.data.get("price_basis") not in PRICE_BASES:
            self.data["price_basis"] = "WORST"

    @staticmethod
    def coerce(typ: str, value: Any) -> Any:
        """Приводит значение к типу настройки; ValueError при ошибке."""
        if typ in ("pct", "float", "money"):
            v = float(D(value, "nan")) if not isinstance(value, (int, float)) else float(value)
            if v != v:
                raise ValueError("NaN")
            if typ == "pct" and not (-100 < v < 1000):
                raise ValueError("range")
            if v < 0 and typ != "pct":
                raise ValueError("negative")
            return v
        if typ == "int":
            v = int(D(value, "nan")) if not isinstance(value, int) else value
            if v < 0:
                raise ValueError("negative")
            return v
        if typ == "bool":
            return to_bool(value)
        if typ == "time":
            if not re.match(r"^\d{1,2}:\d{2}$", str(value).strip()):
                raise ValueError("time")
            h, m = parse_hhmm(str(value))
            return f"{h:02d}:{m:02d}"
        if typ.startswith("choice:"):
            options = typ.split(":", 1)[1].split("|")
            v = str(value).strip()
            if v not in options:
                raise ValueError("choice")
            return v
        if typ == "ids":
            if isinstance(value, list):
                return [int(x) for x in value]
            return [int(x) for x in re.findall(r"-?\d+", str(value or ""))]
        if typ == "regex":
            re.compile(str(value))
            return str(value)
        return str(value if value is not None else "")

    @staticmethod
    def _get_from(data: dict, key: str, default: Any = None) -> Any:
        cur: Any = data
        for part in key.split("."):
            if isinstance(cur, dict) and part in cur:
                cur = cur[part]
            else:
                return default
        return cur

    def get(self, key: str, default: Any = None) -> Any:
        """Возвращает значение по пути через точку."""
        with self.lock:
            v = self._get_from(self.data, key, None)
            if v is None:
                v = self._get_from(DEFAULTS, key, default)
            return v

    def _set_raw(self, key: str, value: Any) -> None:
        parts = key.split(".")
        cur = self.data
        for part in parts[:-1]:
            if not isinstance(cur.get(part), dict):
                cur[part] = {}
            cur = cur[part]
        cur[parts[-1]] = value

    def set(self, key: str, value: Any, save: bool = True) -> None:
        """Устанавливает значение и сохраняет конфиг."""
        with self.lock:
            self._set_raw(key, value)
            if save:
                self.save()

    def dec(self, key: str) -> Decimal:
        return D(self.get(key))

    def admin_ids(self, c: "Cardinal") -> list[int]:
        """Админы: из настроек или авторизованные пользователи Cardinal."""
        ids = [int(x) for x in (self.get("admin_ids") or [])]
        if not ids and c.telegram:
            ids = [int(x) for x in c.telegram.authorized_users.keys()]
        return ids


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# C. DATABASE: SQLite (WAL), один lock, миграции схемы, автобэкапы
# ═══════════════════════════════════════════════════════════════════════════════════════════════

def _exec_script(conn: sqlite3.Connection, script: str) -> None:
    """Выполняет SQL-скрипт по одному выражению (executescript делает COMMIT и ломает транзакцию миграции)."""
    for stmt in script.split(";"):
        if stmt.strip():
            conn.execute(stmt)


def migrate_v0_to_v1(conn: sqlite3.Connection) -> None:
    """Базовая схема."""
    _exec_script(conn, """
    CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT);
    CREATE TABLE IF NOT EXISTS suppliers(
        id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, preset TEXT, profile_json TEXT,
        api_key_enc TEXT, currency TEXT DEFAULT 'USD', enabled INTEGER DEFAULT 1, priority INTEGER DEFAULT 100,
        last_ok_at INTEGER, last_error TEXT);
    CREATE TABLE IF NOT EXISTS services(
        supplier_id INTEGER, service_id TEXT, name TEXT, category TEXT, rate TEXT, min INTEGER, max INTEGER,
        refill INTEGER DEFAULT 0, cancel INTEGER DEFAULT 0, updated_at INTEGER,
        PRIMARY KEY(supplier_id, service_id));
    CREATE TABLE IF NOT EXISTS lots(
        id INTEGER PRIMARY KEY AUTOINCREMENT, fp_lot_id INTEGER, node_id INTEGER, template_id INTEGER,
        title TEXT, mode TEXT, margin_override TEXT, manual_price TEXT, enabled INTEGER DEFAULT 1,
        hidden_reason TEXT, lost INTEGER DEFAULT 0, created_at INTEGER, updated_at INTEGER);
    CREATE TABLE IF NOT EXISTS lot_services(
        lot_id INTEGER, supplier_id INTEGER, service_id TEXT, is_primary INTEGER DEFAULT 0,
        position INTEGER DEFAULT 0, PRIMARY KEY(lot_id, supplier_id, service_id));
    CREATE TABLE IF NOT EXISTS templates(
        id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, title_ru TEXT, title_en TEXT, desc_ru TEXT,
        desc_en TEXT, category_node INTEGER, price_mode TEXT DEFAULT 'per_1000', quantity_pack TEXT,
        secrets_text TEXT, autoreply_text TEXT, created_at INTEGER);
    CREATE TABLE IF NOT EXISTS orders(
        id INTEGER PRIMARY KEY AUTOINCREMENT, fp_order_id TEXT UNIQUE, buyer TEXT, lot_id INTEGER,
        supplier_id INTEGER, service_id TEXT, supplier_order_id TEXT, link TEXT, quantity INTEGER,
        price_paid TEXT, cost TEXT, status TEXT, error TEXT, refunded_amount TEXT DEFAULT '0',
        created_at INTEGER, updated_at INTEGER, completed_at INTEGER, eta_text TEXT);
    CREATE TABLE IF NOT EXISTS order_events(
        id INTEGER PRIMARY KEY AUTOINCREMENT, order_id INTEGER, ts INTEGER, event TEXT, details TEXT);
    CREATE TABLE IF NOT EXISTS service_stats(
        supplier_id INTEGER, service_id TEXT, orders_total INTEGER DEFAULT 0, completed INTEGER DEFAULT 0,
        partial INTEGER DEFAULT 0, canceled INTEGER DEFAULT 0, failed INTEGER DEFAULT 0,
        refills INTEGER DEFAULT 0, avg_seconds INTEGER, rating REAL DEFAULT 0.5, updated_at INTEGER,
        PRIMARY KEY(supplier_id, service_id));
    CREATE TABLE IF NOT EXISTS price_log(
        id INTEGER PRIMARY KEY AUTOINCREMENT, lot_id INTEGER, old TEXT, new TEXT, reason TEXT, ts INTEGER);
    CREATE TABLE IF NOT EXISTS blacklist(buyer TEXT PRIMARY KEY, reason TEXT, ts INTEGER);
    CREATE TABLE IF NOT EXISTS promo(code TEXT PRIMARY KEY, buyer TEXT, percent INTEGER, used INTEGER DEFAULT 0,
        ts INTEGER);
    CREATE TABLE IF NOT EXISTS raise_state(category INTEGER PRIMARY KEY, next_at INTEGER, last_ok INTEGER,
        last_error TEXT);
    """)


def _add_column(conn: sqlite3.Connection, table: str, column: str, decl: str) -> None:
    cols = [r[1] for r in conn.execute(f"PRAGMA table_info({table})").fetchall()]
    if column not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {decl}")


def migrate_v1_to_v2(conn: sqlite3.Connection) -> None:
    """Служебные поля для upsert, конечного автомата заказов, умных скидок; индексы."""
    for col, decl in (("pack_qty", "INTEGER DEFAULT 0"), ("supplier_id", "INTEGER"), ("service_id", "TEXT"),
                      ("price", "TEXT"), ("description", "TEXT"), ("manual_edit", "INTEGER DEFAULT 0"),
                      ("last_sale_at", "INTEGER"), ("discount_active", "INTEGER DEFAULT 0")):
        _add_column(conn, "lots", col, decl)
    for col, decl in (("disabled", "INTEGER DEFAULT 0"), ("prev_rate", "TEXT")):
        _add_column(conn, "services", col, decl)
    for col, decl in (("needs_key", "INTEGER DEFAULT 0"), ("select_mode", "TEXT")):
        _add_column(conn, "suppliers", col, decl)
    for col, decl in (("chat_id", "TEXT"), ("fp_amount", "INTEGER"), ("link_attempts", "INTEGER DEFAULT 0"),
                      ("confirm_deadline", "INTEGER"), ("reminded", "INTEGER DEFAULT 0"),
                      ("next_poll_at", "INTEGER"), ("poll_count", "INTEGER DEFAULT 0"),
                      ("delayed_notified", "INTEGER DEFAULT 0"), ("tried", "TEXT DEFAULT '[]'"),
                      ("remain", "INTEGER"), ("start_count", "INTEGER"), ("supplier_status", "TEXT"),
                      ("last_status_reply", "INTEGER DEFAULT 0"), ("sent_at", "INTEGER"),
                      ("bonus_pct", "INTEGER DEFAULT 0"), ("refund_due", "TEXT"), ("problem", "INTEGER DEFAULT 0")):
        _add_column(conn, "orders", col, decl)
    _exec_script(conn, """
    CREATE UNIQUE INDEX IF NOT EXISTS ux_lots_key ON lots(template_id, supplier_id, service_id, pack_qty)
        WHERE template_id IS NOT NULL;
    CREATE INDEX IF NOT EXISTS ix_lots_fp ON lots(fp_lot_id);
    CREATE INDEX IF NOT EXISTS ix_orders_status ON orders(status);
    CREATE INDEX IF NOT EXISTS ix_orders_chat ON orders(chat_id, status);
    CREATE INDEX IF NOT EXISTS ix_orders_service ON orders(supplier_id, service_id, status);
    CREATE INDEX IF NOT EXISTS ix_events_order ON order_events(order_id);
    CREATE INDEX IF NOT EXISTS ix_price_log_lot ON price_log(lot_id);
    """)


def migrate_v2_to_v3(conn: sqlite3.Connection) -> None:
    """Автопилот: блокировка отправки, повторы возвратов, докрутки, автопауза лотов."""
    for col, decl in (("send_started_at", "INTEGER"), ("refund_attempts", "INTEGER DEFAULT 0"),
                      ("refund_reason", "TEXT"), ("last_refill_at", "INTEGER"),
                      ("confirm_reminded", "INTEGER DEFAULT 0"), ("link_reminded", "INTEGER DEFAULT 0"),
                      ("first_error_at", "INTEGER")):
        _add_column(conn, "orders", col, decl)
    for col, decl in (("auto_paused", "TEXT"), ("auto_margin", "TEXT")):
        _add_column(conn, "lots", col, decl)
    _exec_script(conn, """
    CREATE INDEX IF NOT EXISTS ix_orders_buyer ON orders(buyer, created_at);
    CREATE INDEX IF NOT EXISTS ix_orders_link ON orders(link, status)
    """)


MIGRATIONS: dict[int, Callable[[sqlite3.Connection], None]] = {0: migrate_v0_to_v1, 1: migrate_v1_to_v2,
                                                                2: migrate_v2_to_v3}


class Database:
    """SQLite-хранилище с единым lock, миграциями и бэкапами."""

    def __init__(self, path: str = DB_PATH, keep_backups: int = 5):
        self.path = path
        self.keep_backups = keep_backups
        self.lock = threading.RLock()
        self._secret = self._load_secret()
        self.conn = self._connect()
        self.migrate()

    def _connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.path, check_same_thread=False, timeout=30, isolation_level=None)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA foreign_keys=OFF")
        return conn

    @staticmethod
    def _load_secret() -> bytes:
        if os.path.exists(SECRET_PATH):
            with open(SECRET_PATH, "rb") as f:
                data = f.read()
            if len(data) >= 16:
                return data
        data = pysecrets.token_bytes(32)
        with open(SECRET_PATH, "wb") as f:
            f.write(data)
        return data

    def enc(self, text: Optional[str]) -> str:
        """Обфускация (XOR с локальным ключом + base64). Не криптостойкое шифрование."""
        if not text:
            return ""
        raw = text.encode("utf-8")
        key = self._secret
        return base64.b64encode(bytes(b ^ key[i % len(key)] for i, b in enumerate(raw))).decode()

    def dec(self, text: Optional[str]) -> str:
        if not text:
            return ""
        try:
            raw = base64.b64decode(text.encode())
            key = self._secret
            return bytes(b ^ key[i % len(key)] for i, b in enumerate(raw)).decode("utf-8")
        except Exception:
            log_error("Не удалось расшифровать ключ API (секрет данных изменился?).")
            return ""

    def schema_version(self) -> int:
        with self.lock:
            try:
                row = self.conn.execute("SELECT value FROM meta WHERE key='schema_version'").fetchone()
                return int(row[0]) if row else 0
            except sqlite3.OperationalError:
                return 0

    def migrate(self) -> None:
        """Бэкап и последовательное применение migrate_vN_to_vN+1."""
        current = self.schema_version()
        if current > SCHEMA_VERSION:
            raise RuntimeError(f"База данных создана более новой версией плагина (схема {current} > "
                               f"{SCHEMA_VERSION}). Обновите плагин.")
        if current == SCHEMA_VERSION:
            return
        if current > 0:
            self.backup(f"pre_migrate_v{current}")
        with self.lock:
            for v in range(current, SCHEMA_VERSION):
                log_info(f"Миграция схемы БД v{v} -> v{v + 1}")
                self.conn.execute("BEGIN")
                try:
                    MIGRATIONS[v](self.conn)
                    self.conn.execute("INSERT OR REPLACE INTO meta(key, value) VALUES('schema_version', ?)",
                                      (str(v + 1),))
                    self.conn.execute("COMMIT")
                except Exception:
                    self.conn.execute("ROLLBACK")
                    raise

    @contextmanager
    def transaction(self):
        """Транзакция под общим lock."""
        with self.lock:
            self.conn.execute("BEGIN")
            try:
                yield self.conn
                self.conn.execute("COMMIT")
            except Exception:
                self.conn.execute("ROLLBACK")
                raise

    def execute(self, sql: str, params: tuple | list = ()) -> int:
        with self.lock:
            cur = self.conn.execute(sql, tuple(params))
            return cur.lastrowid if cur.lastrowid else cur.rowcount

    def rowcount(self, sql: str, params: tuple | list = ()) -> int:
        with self.lock:
            return self.conn.execute(sql, tuple(params)).rowcount

    def query(self, sql: str, params: tuple | list = ()) -> list[dict]:
        with self.lock:
            return [dict(r) for r in self.conn.execute(sql, tuple(params)).fetchall()]

    def one(self, sql: str, params: tuple | list = ()) -> Optional[dict]:
        with self.lock:
            r = self.conn.execute(sql, tuple(params)).fetchone()
            return dict(r) if r else None

    def scalar(self, sql: str, params: tuple | list = (), default: Any = None) -> Any:
        with self.lock:
            r = self.conn.execute(sql, tuple(params)).fetchone()
            return r[0] if r and r[0] is not None else default

    def meta_get(self, key: str, default: Any = None) -> Any:
        v = self.scalar("SELECT value FROM meta WHERE key=?", (key,))
        return default if v is None else v

    def meta_set(self, key: str, value: Any) -> None:
        self.execute("INSERT OR REPLACE INTO meta(key, value) VALUES(?, ?)", (key, str(value)))

    def backup(self, reason: str = "auto") -> str:
        """Создаёт бэкап базы (sqlite backup API) и оставляет последние N."""
        ensure_dirs()
        name = f"autosmmway_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{re.sub(r'[^a-z0-9_]', '', reason)}" \
               f"_s{self.schema_version()}.db"
        path = os.path.join(BACKUP_DIR, name)
        with self.lock:
            dst = sqlite3.connect(path)
            try:
                self.conn.backup(dst)
            finally:
                dst.close()
        self._rotate_backups()
        log_info(f"Бэкап базы: {name}")
        return path

    def _rotate_backups(self) -> None:
        files = sorted(self.list_backups(), key=lambda x: x["ts"], reverse=True)
        for item in files[max(1, self.keep_backups):]:
            try:
                os.remove(item["path"])
            except OSError:
                pass

    @staticmethod
    def list_backups() -> list[dict]:
        """Список бэкапов: путь, имя, размер, время, версия схемы."""
        if not os.path.isdir(BACKUP_DIR):
            return []
        result = []
        for name in os.listdir(BACKUP_DIR):
            if not name.endswith(".db"):
                continue
            path = os.path.join(BACKUP_DIR, name)
            m = re.search(r"_s(\d+)\.db$", name)
            result.append({"path": path, "name": name, "size": os.path.getsize(path),
                           "ts": int(os.path.getmtime(path)), "schema": int(m.group(1)) if m else 0})
        return sorted(result, key=lambda x: x["ts"], reverse=True)

    def restore(self, path: str) -> None:
        """Восстанавливает базу из файла бэкапа (предварительно делает новый автобэкап)."""
        if not os.path.exists(path):
            raise FileNotFoundError(path)
        src = sqlite3.connect(path)
        try:
            ver = int((src.execute("SELECT value FROM meta WHERE key='schema_version'").fetchone() or [0])[0])
        finally:
            src.close()
        if ver > SCHEMA_VERSION:
            raise RuntimeError("Бэкап создан более новой версией плагина.")
        self.backup("pre_restore")
        with self.lock:
            src = sqlite3.connect(path)
            try:
                src.backup(self.conn)
            finally:
                src.close()
        self.migrate()
        log_info(f"База восстановлена из {os.path.basename(path)}")

    def close(self) -> None:
        with self.lock:
            try:
                self.conn.close()
            except Exception:
                pass


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# D. HTTP-СЛОЙ И SUPPLIERS: SupplierBase, GenericSupplier, профили, пресеты
# ═══════════════════════════════════════════════════════════════════════════════════════════════

API_ERROR_CODES = ("api_error", "no_balance", "auth", "service", "link", "quantity")


class SupplierError(Exception):
    """Ошибка поставщика: code — машинный код, message — описание."""

    def __init__(self, code: str, message: str, raw: Any = None):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message
        self.raw = raw


_SMM_V2_PROFILE: dict = {
    "name": "SMM-панель",
    "preset": "smm_v2",
    "base_url": "https://example.com/api/v2",
    "auth": {"type": "body_field", "name": "key", "value_ref": "api_key"},
    "request_format": "form",
    "method": "POST",
    "currency": "USD",
    "rate_unit": 1000,
    "endpoints": {
        "services": {"path": "", "extra": {"action": "services"}},
        "add": {"path": "", "extra": {"action": "add"}},
        "status": {"path": "", "extra": {"action": "status"}},
        "balance": {"path": "", "extra": {"action": "balance"}},
        "refill": {"path": "", "extra": {"action": "refill"}},
        "cancel": {"path": "", "extra": {"action": "cancel"}},
    },
    "params_map": {"service_id": "service", "link": "link", "quantity": "quantity", "order_id": "order"},
    "response_map": {
        "services_list": "", "service.id": "service", "service.name": "name", "service.category": "category",
        "service.rate": "rate", "service.min": "min", "service.max": "max", "service.refill": "refill",
        "service.cancel": "cancel", "order_id": "order", "status": "status", "remain": "remain",
        "charge": "charge", "start_count": "start_count", "balance": "balance", "currency": "currency",
        "error": "error",
    },
    "status_map": {
        "Pending": "PENDING", "Processing": "IN_PROGRESS", "In progress": "IN_PROGRESS",
        "Completed": "COMPLETED", "Partial": "PARTIAL", "Canceled": "CANCELED", "Cancelled": "CANCELED",
        "Refunded": "CANCELED", "Fail": "FAILED", "Failed": "FAILED", "Error": "FAILED",
    },
    "timeout": 20,
    "retries": 3,
    "rate_limit_per_sec": 3,
}

PRESETS: dict[str, dict] = {
    "smm_v2": {"title": "Стандартная SMM-панель (API v2)", "profile": _SMM_V2_PROFILE},
    "smmway": {"title": "SMMway (по умолчанию)",
               "profile": deep_merge(_SMM_V2_PROFILE, {"name": "SMMway", "preset": "smmway",
                                                       # Проверьте актуальный адрес API в личном кабинете SMMway.
                                                       "base_url": "https://smmway.ru/api/v2"})},
    "rest_custom": {"title": "REST (ручная настройка)", "profile": {
        "name": "REST API", "preset": "rest_custom", "base_url": "", "auth": {"type": "header",
                                                                                "name": "Authorization",
                                                                                "value_ref": "api_key"},
        "request_format": "json", "method": "POST", "currency": "USD", "rate_unit": 1000,
        "endpoints": {k: {"path": "", "extra": {}} for k in ("services", "add", "status", "balance", "refill",
                                                             "cancel")},
        "params_map": {"service_id": "service", "link": "link", "quantity": "quantity", "order_id": "order"},
        "response_map": {k: "" for k in _SMM_V2_PROFILE["response_map"]},
        "status_map": {}, "timeout": 20, "retries": 3, "rate_limit_per_sec": 3}},
}

PROFILE_REQUIRED_KEYS = ("base_url", "auth", "request_format", "method", "currency", "rate_unit", "endpoints",
                         "params_map", "response_map", "status_map")


def validate_profile(profile: Any) -> list[str]:
    """Возвращает список ошибок профиля (пустой — профиль корректен)."""
    errors = []
    if not isinstance(profile, dict):
        return ["профиль должен быть JSON-объектом"]
    for k in PROFILE_REQUIRED_KEYS:
        if k not in profile:
            errors.append(f"нет поля «{k}»")
    if errors:
        return errors
    if not re.match(r"^https?://\S+$", str(profile.get("base_url") or "")):
        errors.append("base_url должен начинаться с http(s)://")
    auth = profile.get("auth") or {}
    if not isinstance(auth, dict) or auth.get("type") not in ("body_field", "header", "bearer", "query", "none"):
        errors.append("auth.type: body_field | header | bearer | query | none")
    if profile.get("request_format") not in ("form", "json"):
        errors.append("request_format: form | json")
    if str(profile.get("method", "")).upper() not in ("GET", "POST"):
        errors.append("method: GET | POST")
    if to_int(profile.get("rate_unit"), 0) <= 0:
        errors.append("rate_unit должен быть > 0")
    for name in ("services", "add", "status", "balance"):
        ep = (profile.get("endpoints") or {}).get(name)
        if not isinstance(ep, dict):
            errors.append(f"endpoints.{name} должен быть объектом {{path, extra}}")
    for name in ("params_map", "response_map", "status_map"):
        if not isinstance(profile.get(name), dict):
            errors.append(f"{name} должен быть объектом")
    for v in (profile.get("status_map") or {}).values():
        if v not in INTERNAL_SUPPLIER_STATUSES:
            errors.append(f"status_map: неизвестный внутренний статус {v}")
            break
    return errors


def json_path_get(data: Any, path: Optional[str], default: Any = None) -> Any:
    """JSON-путь через точку с индексами: «data.items.0.id» или «data.items[0].id». Пустой путь — сам объект."""
    if path is None:
        return default
    path = str(path).strip()
    if path == "":
        return data
    path = re.sub(r"\[(\d+)\]", r".\1", path)
    cur = data
    for part in [p for p in path.split(".") if p != ""]:
        if isinstance(cur, dict):
            if part in cur:
                cur = cur[part]
            else:
                return default
        elif isinstance(cur, list):
            if re.fullmatch(r"-?\d+", part) and -len(cur) <= int(part) < len(cur):
                cur = cur[int(part)]
            else:
                return default
        else:
            return default
    return cur


class RateLimiter:
    """Ограничение частоты запросов (запросов в секунду)."""

    def __init__(self, per_sec: float):
        self.interval = 1.0 / per_sec if per_sec and per_sec > 0 else 0
        self.lock = threading.Lock()
        self.last = 0.0

    def wait(self) -> None:
        if not self.interval:
            return
        with self.lock:
            delta = time.monotonic() - self.last
            if delta < self.interval:
                time.sleep(self.interval - delta)
            self.last = time.monotonic()


class CircuitBreaker:
    """N ошибок подряд -> пауза поставщика."""

    def __init__(self, max_errors: int = 3, pause: int = 600):
        self.max_errors = max_errors
        self.pause = pause
        self.errors = 0
        self.open_until = 0.0
        self.lock = threading.Lock()

    @property
    def is_open(self) -> bool:
        return time.time() < self.open_until

    def ok(self) -> None:
        with self.lock:
            self.errors = 0

    def fail(self) -> bool:
        """Регистрирует ошибку; True — если breaker только что сработал."""
        with self.lock:
            self.errors += 1
            if self.errors >= self.max_errors and not self.is_open:
                self.open_until = time.time() + self.pause
                self.errors = 0
                return True
            return False

    def reset(self) -> None:
        with self.lock:
            self.errors = 0
            self.open_until = 0


class SupplierBase:
    """Базовый интерфейс поставщика."""

    id: int = 0
    name: str = ""
    currency: str = "USD"
    rate_unit: int = 1000

    def get_services(self) -> list[dict]:
        raise NotImplementedError

    def get_balance(self) -> tuple[Decimal, str]:
        raise NotImplementedError

    def create_order(self, service_id: str, link: str, quantity: int) -> str:
        raise NotImplementedError

    def get_status(self, order_id: str) -> dict:
        raise NotImplementedError

    def refill(self, order_id: str) -> Any:
        raise NotImplementedError

    def cancel(self, order_id: str) -> Any:
        raise NotImplementedError

    def ping(self) -> int:
        raise NotImplementedError

    @staticmethod
    def create_from_profile(profile: dict, api_key: str = "", supplier_id: int = 0,
                            dry_run: Callable[[], bool] = lambda: False,
                            on_breaker: Optional[Callable[[SupplierBase], None]] = None,
                            circuit_errors: int = 3, circuit_pause: int = 600) -> "GenericSupplier":
        """Фабрика: создаёт GenericSupplier по профилю."""
        return GenericSupplier(profile, api_key, supplier_id, dry_run, on_breaker, circuit_errors, circuit_pause)


class GenericSupplier(SupplierBase):
    """Поставщик, полностью описанный профилем (SMM API v2, произвольный REST)."""

    def __init__(self, profile: dict, api_key: str, supplier_id: int = 0,
                 dry_run: Callable[[], bool] = lambda: False,
                 on_breaker: Optional[Callable[[SupplierBase], None]] = None,
                 circuit_errors: int = 3, circuit_pause: int = 600):
        self.profile = profile
        self.api_key = api_key or ""
        self.id = supplier_id
        self.name = str(profile.get("name") or f"Поставщик {supplier_id}")
        self.currency = str(profile.get("currency") or "USD").upper()
        self.rate_unit = max(1, to_int(profile.get("rate_unit"), 1000))
        self.timeout = max(3, to_int(profile.get("timeout"), 20))
        self.retries = max(1, to_int(profile.get("retries"), 3))
        self.limiter = RateLimiter(float(D(profile.get("rate_limit_per_sec"), "3")))
        self.breaker = CircuitBreaker(circuit_errors, circuit_pause)
        self.dry_run = dry_run
        self.on_breaker = on_breaker
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": USER_AGENT, "Accept": "application/json, */*"})
        self.last_raw: str = ""

    # ── низкоуровневый запрос ──
    def _map_param(self, internal: str) -> str:
        return str((self.profile.get("params_map") or {}).get(internal) or internal)

    def _resp_path(self, key: str) -> Optional[str]:
        rm = self.profile.get("response_map") or {}
        return rm.get(key) if key in rm else None

    def _build(self, endpoint: str, params: dict) -> tuple[str, str, dict, dict, dict]:
        ep = (self.profile.get("endpoints") or {}).get(endpoint)
        if not isinstance(ep, dict):
            raise SupplierError("not_supported", f"эндпоинт «{endpoint}» не настроен")
        base = str(self.profile.get("base_url") or "").rstrip("/")
        path = str(ep.get("path") or "")
        for k, v in params.items():
            path = path.replace("{" + k + "}", str(v))
        url = base + (("/" + path.lstrip("/")) if path else "")
        method = str(ep.get("method") or self.profile.get("method") or "POST").upper()
        body: dict = dict(ep.get("extra") or {})
        for k, v in params.items():
            if "{" + k + "}" not in str(ep.get("path") or ""):
                body[self._map_param(k)] = v
        headers: dict = {}
        query: dict = {}
        auth = self.profile.get("auth") or {}
        atype = auth.get("type", "body_field")
        aname = auth.get("name") or "key"
        if atype == "body_field":
            body[aname] = self.api_key
        elif atype == "header":
            headers[aname] = self.api_key
        elif atype == "bearer":
            headers["Authorization"] = f"Bearer {self.api_key}"
        elif atype == "query":
            query[aname] = self.api_key
        if method == "GET":
            query.update(body)
            body = {}
        return method, url, body, headers, query

    @staticmethod
    def classify_api_error(message: str) -> str:
        """Код ошибки API по тексту: no_balance, auth, service, link, quantity, api_error."""
        m = message.lower()
        if any(x in m for x in ("balance", "funds", "баланс", "средств", "insufficient", "not enough")):
            return "no_balance"
        if any(x in m for x in ("api key", "invalid key", "incorrect key", "ключ", "unauthor", "auth", "token",
                                "forbidden", "access denied")):
            return "auth"
        if any(x in m for x in ("service", "услуг", "disabled", "not available", "unavailable", "inactive")):
            return "service"
        if any(x in m for x in ("link", "url", "ссылк", "private", "закрыт", "username")):
            return "link"
        if any(x in m for x in ("quantity", "количеств", "min", "max")):
            return "quantity"
        return "api_error"

    @staticmethod
    def _sent_before_failure(exc: Exception) -> bool:
        """True — запрос мог дойти до сервера (повтор небезопасен для неидемпотентных методов)."""
        if isinstance(exc, requests.ConnectTimeout):
            return False
        text = str(exc)
        if isinstance(exc, requests.ConnectionError) and any(
                x in text for x in ("NewConnectionError", "Failed to establish", "Name or service not known",
                                    "getaddrinfo", "Connection refused", "No route to host", "ProxyError")):
            return False
        return True

    def _request(self, endpoint: str, params: Optional[dict] = None, use_breaker: bool = True) -> Any:
        params = params or {}
        # «add» неидемпотентен: повтор после того, как запрос дошёл до сервера, может создать второй заказ.
        unsafe = endpoint == "add"
        if use_breaker and self.breaker.is_open:
            raise SupplierError("circuit_open", f"поставщик на паузе до "
                                                f"{datetime.fromtimestamp(self.breaker.open_until):%H:%M}")
        method, url, body, headers, query = self._build(endpoint, params)
        delays = [1, 3, 7]
        last_error: Optional[SupplierError] = None
        for attempt in range(self.retries):
            self.limiter.wait()
            try:
                if self.profile.get("request_format") == "json" and method != "GET":
                    resp = self.session.request(method, url, json=body, headers=headers, params=query,
                                                timeout=self.timeout)
                else:
                    resp = self.session.request(method, url, data=body if method != "GET" else None,
                                                headers=headers, params=query, timeout=self.timeout)
                self.last_raw = resp.text[:2000]
                if resp.status_code == 429:
                    raise SupplierError("http_429", "HTTP 429 (лимит запросов)", resp.text[:500])
                if resp.status_code >= 500:
                    # 502/503 — шлюз не передал запрос приложению, повтор безопасен; 500/504 — результат неизвестен.
                    if unsafe and resp.status_code not in (502, 503):
                        raise SupplierError("uncertain", f"HTTP {resp.status_code} на создании заказа — "
                                                         f"заказ мог быть создан", resp.text[:500])
                    raise SupplierError(f"http_{resp.status_code}", f"HTTP {resp.status_code}", resp.text[:500])
                try:
                    data = resp.json()
                except ValueError:
                    if unsafe and resp.status_code < 400:
                        raise SupplierError("uncertain", "ответ на создание заказа не JSON — заказ мог быть создан",
                                            resp.text[:500])
                    raise SupplierError("bad_json", f"ответ не JSON (HTTP {resp.status_code})", resp.text[:500])
                err_path = self._resp_path("error")
                err = json_path_get(data, err_path) if err_path and isinstance(data, dict) else None
                if err:
                    # Ошибки уровня API не ретраим: это ответ сервера, а не сбой сети.
                    self.breaker.ok()
                    if resp.status_code in (401, 403):
                        raise SupplierError("auth", str(err)[:300], data)
                    raise SupplierError(self.classify_api_error(str(err)), str(err)[:300], data)
                if resp.status_code in (401, 403):
                    raise SupplierError("auth", f"HTTP {resp.status_code}: доступ запрещён (проверьте ключ)",
                                        resp.text[:500])
                if resp.status_code >= 400:
                    raise SupplierError(f"http_{resp.status_code}", f"HTTP {resp.status_code}", resp.text[:500])
                self.breaker.ok()
                return data
            except SupplierError as e:
                if e.code in API_ERROR_CODES or e.code == "uncertain":
                    raise
                last_error = e
            except requests.RequestException as e:
                text = str(e).replace(self.api_key, mask_secret(self.api_key)) if self.api_key else str(e)
                if unsafe and self._sent_before_failure(e):
                    raise SupplierError("uncertain", f"обрыв связи после отправки заказа ({text[:120]}) — "
                                                     f"заказ мог быть создан")
                if isinstance(e, requests.Timeout):
                    last_error = SupplierError("timeout", f"таймаут {self.timeout} c")
                else:
                    last_error = SupplierError("network", text[:200])
            log_warn(f"{self.name}: {endpoint} попытка {attempt + 1}/{self.retries}: {last_error.message}")
            if attempt < self.retries - 1:
                time.sleep(delays[min(attempt, len(delays) - 1)])
        if use_breaker and self.breaker.fail():
            log_error(f"{self.name}: circuit breaker — пауза {self.breaker.pause} c")
            if self.on_breaker:
                try:
                    self.on_breaker(self)
                except Exception:
                    log_error("on_breaker", exc=True)
        raise last_error or SupplierError("unknown", "неизвестная ошибка")

    # ── разбор ответов ──
    def _services_list(self, data: Any) -> list:
        lst = json_path_get(data, self._resp_path("services_list") or "")
        if isinstance(lst, dict):
            values = list(lst.values())
            if values and all(isinstance(v, dict) for v in values):
                out = []
                for k, v in lst.items():
                    item = dict(v)
                    item.setdefault("__key", k)
                    out.append(item)
                return out
            return [lst]
        return lst if isinstance(lst, list) else []

    def parse_services(self, data: Any) -> list[dict]:
        """Приводит каталог поставщика к единому виду."""
        result = []
        for item in self._services_list(data):
            if not isinstance(item, dict):
                continue

            def g(key: str, default: Any = None) -> Any:
                path = self._resp_path(f"service.{key}")
                return json_path_get(item, path, default) if path else default

            sid = g("id") if g("id") is not None else item.get("__key")
            rate = g("rate")
            if sid is None or rate is None:
                continue
            result.append({
                "service_id": str(sid),
                "name": str(g("name", "") or f"Услуга {sid}"),
                "category": str(g("category", "") or "Без категории"),
                "rate": str(D(rate)),
                "min": to_int(g("min"), 1) or 1,
                "max": to_int(g("max"), 1000000) or 1000000,
                "refill": 1 if to_bool(g("refill")) else 0,
                "cancel": 1 if to_bool(g("cancel")) else 0,
            })
        return result

    def normalize_status(self, raw: Any) -> str:
        """Нормализует статус поставщика через status_map; неизвестный -> IN_PROGRESS с логом."""
        smap = self.profile.get("status_map") or {}
        s = str(raw or "").strip()
        if s in smap:
            return smap[s]
        low = {str(k).lower(): v for k, v in smap.items()}
        if s.lower() in low:
            return low[s.lower()]
        if s.upper() in INTERNAL_SUPPLIER_STATUSES:
            return s.upper()
        log_warn(f"{self.name}: неизвестный статус «{s}», считаю IN_PROGRESS")
        return "IN_PROGRESS"

    # ── публичные методы ──
    def get_services(self) -> list[dict]:
        """Каталог услуг поставщика."""
        return self.parse_services(self._request("services"))

    def get_balance(self) -> tuple[Decimal, str]:
        """Баланс и валюта."""
        data = self._request("balance")
        bal = json_path_get(data, self._resp_path("balance") or "balance")
        if bal is None:
            raise SupplierError("parse", "не найден баланс в ответе", data)
        cur = json_path_get(data, self._resp_path("currency") or "currency") or self.currency
        return D(bal), str(cur).upper()

    def create_order(self, service_id: str, link: str, quantity: int) -> str:
        """Создаёт заказ, возвращает ID заказа у поставщика."""
        if self.dry_run():
            fake = f"DRY-{pysecrets.token_hex(4)}"
            log_info(f"[DRY-RUN] {self.name}: add service={service_id} qty={quantity} link={mask_link(link)} -> {fake}")
            return fake
        data = self._request("add", {"service_id": service_id, "link": link, "quantity": int(quantity)})
        oid = json_path_get(data, self._resp_path("order_id") or "order")
        if oid in (None, "", 0, "0"):
            raise SupplierError("parse", "в ответе нет номера заказа", data)
        log_info(f"{self.name}: заказ создан #{oid} service={service_id} qty={quantity} link={mask_link(link)}")
        return str(oid)

    def get_status(self, order_id: str) -> dict:
        """Статус заказа: status (внутренний), raw_status, remain, charge, start_count."""
        if str(order_id).startswith("DRY-"):
            return {"status": "COMPLETED", "raw_status": "dry-run", "remain": 0, "charge": None,
                    "start_count": None}
        data = self._request("status", {"order_id": order_id})
        if isinstance(data, dict) and str(order_id) in data and isinstance(data[str(order_id)], dict):
            data = data[str(order_id)]
        raw = json_path_get(data, self._resp_path("status") or "status")
        if raw is None:
            raise SupplierError("parse", "в ответе нет статуса", data)
        remain = json_path_get(data, self._resp_path("remain") or "remain")
        charge = json_path_get(data, self._resp_path("charge") or "charge")
        start = json_path_get(data, self._resp_path("start_count") or "start_count")
        return {"status": self.normalize_status(raw), "raw_status": str(raw),
                "remain": to_int(remain, 0) if remain is not None else None,
                "charge": str(D(charge)) if charge not in (None, "") else None,
                "start_count": to_int(start, 0) if start not in (None, "") else None}

    def refill(self, order_id: str) -> Any:
        """Запрос докрутки."""
        if self.dry_run() or str(order_id).startswith("DRY-"):
            log_info(f"[DRY-RUN] {self.name}: refill {order_id}")
            return {"dry_run": True}
        return self._request("refill", {"order_id": order_id})

    def cancel(self, order_id: str) -> Any:
        """Запрос отмены."""
        if self.dry_run() or str(order_id).startswith("DRY-"):
            log_info(f"[DRY-RUN] {self.name}: cancel {order_id}")
            return {"dry_run": True}
        ep = (self.profile.get("endpoints") or {}).get("cancel") or {}
        if (ep.get("extra") or {}).get("action") == "cancel" and self.profile.get("preset") in ("smm_v2", "smmway"):
            return self._request("cancel", {"orders": order_id})
        return self._request("cancel", {"order_id": order_id})

    def ping(self) -> int:
        """Пинг через запрос баланса, мс."""
        t = time.monotonic()
        self._request("balance", use_breaker=False)
        return int((time.monotonic() - t) * 1000)


class SupplierManager:
    """Профили поставщиков в БД, экземпляры GenericSupplier, кэш каталога и балансов."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.db = p.db
        self.lock = threading.RLock()
        self._instances: dict[int, GenericSupplier] = {}
        self._balances: dict[int, tuple[float, Decimal, str]] = {}

    def _on_breaker(self, s: SupplierBase) -> None:
        self.db.execute("UPDATE suppliers SET last_error=? WHERE id=?", ("circuit breaker", s.id))
        self.p.alerts.send(f"⛔ Поставщик <b>{esc(s.name)}</b>: серия ошибок, пауза "
                           f"{self.p.cfg.get('circuit_pause')} c.", key=f"breaker:{s.id}")

    def list(self, enabled_only: bool = False) -> list[dict]:
        sql = "SELECT * FROM suppliers" + (" WHERE enabled=1 AND needs_key=0" if enabled_only else "") + \
              " ORDER BY priority, id"
        return self.db.query(sql)

    def row(self, sid: int) -> Optional[dict]:
        return self.db.one("SELECT * FROM suppliers WHERE id=?", (sid,))

    def profile(self, sid: int) -> dict:
        r = self.row(sid)
        if not r:
            return {}
        try:
            return json.loads(r["profile_json"] or "{}")
        except ValueError:
            return {}

    def get(self, sid: int) -> Optional[GenericSupplier]:
        """Экземпляр поставщика (кэшируется)."""
        with self.lock:
            if sid in self._instances:
                return self._instances[sid]
            r = self.row(sid)
            if not r:
                return None
            prof = self.profile(sid)
            prof["name"] = r["name"]
            inst = SupplierBase.create_from_profile(
                prof, self.db.dec(r["api_key_enc"]), sid, lambda: bool(self.p.cfg.get("dry_run")),
                self._on_breaker, int(self.p.cfg.get("circuit_errors")), int(self.p.cfg.get("circuit_pause")))
            self._instances[sid] = inst
            return inst

    def invalidate(self, sid: Optional[int] = None) -> None:
        with self.lock:
            if sid is None:
                self._instances.clear()
                self._balances.clear()
            else:
                self._instances.pop(sid, None)
                self._balances.pop(sid, None)

    def add(self, profile: dict, api_key: str, enabled: bool = True, priority: int = 100,
            needs_key: bool = False) -> int:
        """Добавляет поставщика, возвращает id."""
        sid = self.db.execute(
            "INSERT INTO suppliers(name, preset, profile_json, api_key_enc, currency, enabled, priority, needs_key)"
            " VALUES(?,?,?,?,?,?,?,?)",
            (profile.get("name") or "Поставщик", profile.get("preset") or "rest_custom",
             json.dumps(profile, ensure_ascii=False), self.db.enc(api_key), str(profile.get("currency") or "USD"),
             1 if enabled and not needs_key else 0, priority, 1 if needs_key else 0))
        log_info(f"Добавлен поставщик #{sid} {profile.get('name')} (ключ {mask_secret(api_key)})")
        return sid

    def update_profile(self, sid: int, profile: dict) -> None:
        self.db.execute("UPDATE suppliers SET profile_json=?, currency=?, name=? WHERE id=?",
                        (json.dumps(profile, ensure_ascii=False), str(profile.get("currency") or "USD"),
                         profile.get("name") or "Поставщик", sid))
        self.invalidate(sid)

    def set_key(self, sid: int, api_key: str) -> None:
        self.db.execute("UPDATE suppliers SET api_key_enc=?, needs_key=0 WHERE id=?", (self.db.enc(api_key), sid))
        self.invalidate(sid)
        log_info(f"Поставщик #{sid}: ключ обновлён ({mask_secret(api_key)})")

    def set_field(self, sid: int, column: str, value: Any) -> None:
        if column not in ("enabled", "priority", "select_mode", "name", "needs_key"):
            raise ValueError(column)
        self.db.execute(f"UPDATE suppliers SET {column}=? WHERE id=?", (value, sid))
        if column == "name":
            prof = self.profile(sid)
            prof["name"] = value
            self.db.execute("UPDATE suppliers SET profile_json=? WHERE id=?", (json.dumps(prof, ensure_ascii=False),
                                                                             sid))
        self.invalidate(sid)

    def duplicate(self, sid: int) -> int:
        r = self.row(sid)
        prof = self.profile(sid)
        prof["name"] = f"{r['name']} (копия)"
        return self.add(prof, self.db.dec(r["api_key_enc"]), enabled=False, priority=r["priority"] + 1)

    def bound_lots(self, sid: int) -> int:
        return int(self.db.scalar("SELECT COUNT(DISTINCT lot_id) FROM lot_services WHERE supplier_id=?", (sid,), 0))

    def delete(self, sid: int) -> None:
        with self.db.transaction() as conn:
            conn.execute("DELETE FROM lot_services WHERE supplier_id=?", (sid,))
            conn.execute("DELETE FROM services WHERE supplier_id=?", (sid,))
            conn.execute("DELETE FROM suppliers WHERE id=?", (sid,))
        self.invalidate(sid)

    def mark_ok(self, sid: int) -> None:
        self.db.execute("UPDATE suppliers SET last_ok_at=?, last_error=NULL WHERE id=?", (now_ts(), sid))

    def mark_error(self, sid: int, error: str) -> None:
        self.db.execute("UPDATE suppliers SET last_error=? WHERE id=?", (error[:300], sid))

    # ── каталог ──
    def catalog_age(self, sid: int) -> Optional[int]:
        ts = self.db.scalar("SELECT MAX(updated_at) FROM services WHERE supplier_id=?", (sid,))
        return now_ts() - int(ts) if ts else None

    def refresh_catalog(self, sid: int, force: bool = False) -> int:
        """Обновляет кэш каталога (TTL из настроек). Возвращает число услуг."""
        age = self.catalog_age(sid)
        if not force and age is not None and age < int(self.p.cfg.get("catalog_ttl")):
            return int(self.db.scalar("SELECT COUNT(*) FROM services WHERE supplier_id=?", (sid,), 0))
        s = self.get(sid)
        if not s:
            raise SupplierError("not_found", "поставщик не найден")
        try:
            items = s.get_services()
        except SupplierError as e:
            self.mark_error(sid, e.message)
            raise
        self.mark_ok(sid)
        ts = now_ts()
        rise_pct = D(self.p.cfg.get("alerts.price_rise_pct"))
        risen: list[str] = []
        with self.db.transaction() as conn:
            old = {r["service_id"]: r for r in
                   (dict(x) for x in conn.execute("SELECT service_id, rate, disabled FROM services WHERE supplier_id=?",
                                                  (sid,)).fetchall())}
            seen = set()
            for it in items:
                seen.add(it["service_id"])
                prev = old.get(it["service_id"])
                prev_rate = prev["rate"] if prev else None
                if prev_rate and D(prev_rate) > 0 and rise_pct > 0:
                    delta = (D(it["rate"]) - D(prev_rate)) / D(prev_rate) * 100
                    if delta > rise_pct:
                        risen.append(f"{it['service_id']} {it['name'][:40]}: {prev_rate} → {it['rate']} "
                                     f"(+{delta:.1f}%)")
                conn.execute(
                    "INSERT INTO services(supplier_id, service_id, name, category, rate, min, max, refill, cancel,"
                    " updated_at, disabled, prev_rate) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"
                    " ON CONFLICT(supplier_id, service_id) DO UPDATE SET name=excluded.name,"
                    " category=excluded.category, rate=excluded.rate, min=excluded.min, max=excluded.max,"
                    " refill=excluded.refill, cancel=excluded.cancel, updated_at=excluded.updated_at,"
                    " prev_rate=services.rate,"
                    " disabled=CASE WHEN services.disabled=2 THEN 0 ELSE services.disabled END",
                    (sid, it["service_id"], it["name"], it["category"], it["rate"], it["min"], it["max"],
                     it["refill"], it["cancel"], ts, prev["disabled"] if prev else 0, prev_rate))
            for svc_id in set(old) - seen:
                conn.execute("UPDATE services SET disabled=2, updated_at=? WHERE supplier_id=? AND service_id=?",
                             (ts, sid, svc_id))
        if risen:
            self.p.alerts.send(f"📈 <b>{esc(s.name)}</b>: рост закупочной цены:\n" +
                               "\n".join(esc(x) for x in risen[:15]), key=f"rise:{sid}")
        log_info(f"{s.name}: каталог обновлён, услуг {len(items)}")
        return len(items)

    def categories(self, sid: int) -> list[str]:
        return [r["category"] for r in self.db.query(
            "SELECT DISTINCT category FROM services WHERE supplier_id=? AND disabled<2 ORDER BY category", (sid,))]

    def services(self, sid: int, category: Optional[str] = None, text: Optional[str] = None,
                 include_disabled: bool = True) -> list[dict]:
        sql = "SELECT * FROM services WHERE supplier_id=?"
        params: list = [sid]
        if category is not None:
            sql += " AND category=?"
            params.append(category)
        if text:
            sql += " AND (LOWER(name) LIKE ? OR service_id=?)"
            params += [f"%{text.lower()}%", text]
        sql += " AND disabled<2" if include_disabled else " AND disabled=0"
        sql += " ORDER BY CAST(rate AS REAL), CAST(service_id AS INTEGER)"
        return self.db.query(sql, params)

    def service(self, sid: int, service_id: str) -> Optional[dict]:
        return self.db.one("SELECT * FROM services WHERE supplier_id=? AND service_id=?", (sid, str(service_id)))

    def invalidate_balance(self, sid: int) -> None:
        self._balances.pop(sid, None)

    def balance(self, sid: int, max_age: int = 300) -> tuple[Optional[Decimal], str]:
        """Баланс поставщика с кэшем."""
        cached = self._balances.get(sid)
        if cached and time.time() - cached[0] < max_age:
            return cached[1], cached[2]
        s = self.get(sid)
        if not s:
            return None, ""
        try:
            bal, cur = s.get_balance()
            self._balances[sid] = (time.time(), bal, cur)
            self.mark_ok(sid)
            return bal, cur
        except SupplierError as e:
            self.mark_error(sid, e.message)
            return (cached[1], cached[2]) if cached else (None, s.currency)

    def test(self, sid: int) -> str:
        """Тест подключения: баланс + каталог, текст для Telegram."""
        s = self.get(sid)
        if not s:
            return "Поставщик не найден."
        lines = []
        ok = True
        try:
            bal, cur = s.get_balance()
            self._balances[sid] = (time.time(), bal, cur)
            lines.append(f"✅ Баланс: <b>{money(bal)} {esc(cur)}</b>")
        except SupplierError as e:
            ok = False
            lines.append(f"❌ Баланс: {esc(e.message)}")
            if s.last_raw:
                lines.append(f"<code>{esc(s.last_raw[:500])}</code>")
        try:
            n = self.refresh_catalog(sid, force=True)
            sample = self.db.one("SELECT * FROM services WHERE supplier_id=? AND disabled<2 LIMIT 1", (sid,))
            if n and sample:
                lines.append(f"✅ Найдено услуг: <b>{n}</b>\nПример: <code>{esc(sample['service_id'])}</code> "
                             f"{esc(sample['name'][:80])} — {esc(sample['rate'])} {esc(s.currency)} за "
                             f"{s.rate_unit}, мин {sample['min']}, макс {sample['max']}")
            else:
                ok = False
                lines.append("⚠️ Каталог пуст или не разобран. Сырой ответ:")
                lines.append(f"<code>{esc(s.last_raw[:500])}</code>")
        except SupplierError as e:
            ok = False
            lines.append(f"❌ Каталог: {esc(e.message)}")
            if s.last_raw:
                lines.append(f"<code>{esc(s.last_raw[:500])}</code>")
        if not ok:
            lines.append("\nПроверьте URL/ключ или поправьте response_map в редакторе профиля.")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# E. PRICING: PriceEngine, курс валют, PriceMonitor
# ═══════════════════════════════════════════════════════════════════════════════════════════════

class FxRates:
    """Курс валют к рублю: FunPay (через Cardinal), ЦБ РФ или вручную; при сбое — последний сохранённый."""

    CBR_URL = "https://www.cbr-xml-daily.ru/daily_json.js"

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.lock = threading.Lock()
        self.cache: dict[str, tuple[float, Decimal]] = {}

    def _saved(self, cur: str) -> Optional[Decimal]:
        v = self.p.db.meta_get(f"fx:{cur}")
        return D(v) if v else None

    def _fetch(self, cur: str) -> Decimal:
        source = self.p.cfg.get("fx.source")
        if source == "manual":
            v = self.p.cfg.get(f"fx.manual.{cur}")
            if v is None:
                raise ValueError(f"нет ручного курса для {cur}")
            return D(v)
        if source == "funpay" and cur in ("USD", "EUR"):
            rate = self.p.c.get_exchange_rate(getattr(Currency, cur), Currency.RUB, min_interval=600)
            return D(rate)
        resp = requests.get(self.CBR_URL, timeout=15, headers={"User-Agent": USER_AGENT})
        data = resp.json()
        val = data["Valute"][cur]
        return D(val["Value"]) / D(val["Nominal"])

    def rate(self, cur: str) -> Decimal:
        """Сколько рублей стоит 1 единица валюты."""
        cur = (cur or "RUB").upper()
        if cur in ("RUB", "RUR"):
            return Decimal("1")
        interval = int(self.p.cfg.get("fx.interval_min")) * 60
        with self.lock:
            cached = self.cache.get(cur)
            if cached and time.time() - cached[0] < interval:
                return cached[1]
            try:
                value = self._fetch(cur)
                if value <= 0:
                    raise ValueError("курс <= 0")
                self.cache[cur] = (time.time(), value)
                self.p.db.meta_set(f"fx:{cur}", str(value))
                self.p.db.meta_set(f"fx:{cur}:ts", now_ts())
                return value
            except Exception as e:
                saved = self._saved(cur)
                log_warn(f"Курс {cur} недоступен ({e}); последний сохранённый: {saved}")
                self.p.alerts.send(f"💱 Ошибка получения курса {cur}: {esc(str(e)[:150])}. "
                                   f"Использую последний сохранённый: {saved}", key=f"fx:{cur}")
                if saved:
                    self.cache[cur] = (time.time() - interval + 300, saved)
                    return saved
                manual = self.p.cfg.get(f"fx.manual.{cur}")
                if manual:
                    return D(manual)
                raise SupplierError("fx", f"нет курса {cur}")


class PriceEngine:
    """Расчёт себестоимости и цены. Все деньги — Decimal."""

    def __init__(self, p: "AutoSMM"):
        self.p = p

    def fees(self) -> dict[str, Decimal]:
        cfg = self.p.cfg
        return {"fp": cfg.dec("fp_fee") / 100, "wd": cfg.dec("withdraw_fee") / 100, "fixed": cfg.dec("fixed_fee"),
                "buffer": cfg.dec("rate_buffer") / 100, "step": cfg.dec("round_step"),
                "min_profit": cfg.dec("min_profit_abs")}

    def k(self) -> Decimal:
        f = self.fees()
        return (1 - f["fp"]) * (1 - f["wd"])

    def cost_rub(self, rate: Any, rate_unit: int, qty: int, currency: str) -> Decimal:
        """cost_rub = rate × (qty / rate_unit) × fx × (1 + rate_buffer)."""
        f = self.fees()
        return D(rate) * (D(qty) / D(max(1, rate_unit))) * self.p.fx.rate(currency) * (1 + f["buffer"])

    @staticmethod
    def round_up(value: Decimal, step: Decimal) -> Decimal:
        if step <= 0:
            return value.quantize(Decimal("0.01"), rounding=ROUND_CEILING)
        return ((value / step).to_integral_value(rounding=ROUND_CEILING) * step).quantize(Decimal("0.01"))

    def final_price(self, cost: Decimal, margin_pct: Decimal, unit: int = 1000) -> Decimal:
        """price = cost×(1+m)/k + fixed; не ниже cost + min_profit/k; округление вверх до шага."""
        f = self.fees()
        k = self.k()
        if k <= 0:
            raise ValueError("комиссии >= 100%")
        price = cost * (1 + margin_pct / 100) / k + f["fixed"]
        floor = cost + f["min_profit"] / k
        price = max(price, floor)
        step = f["step"] if unit > 1 else min(f["step"], Decimal("0.01"))
        return self.round_up(price, step)

    def profit(self, price: Decimal, cost: Decimal) -> Decimal:
        """Чистая прибыль: (price − fixed) × k − cost."""
        return ((D(price) - self.fees()["fixed"]) * self.k() - D(cost)).quantize(Decimal("0.01"))

    def margin_for(self, lot: Optional[dict], svc: dict) -> tuple[Decimal, str]:
        """Приоритет: лот > услуга > категория > по умолчанию (+ умная скидка)."""
        cfg = self.p.cfg
        if lot and lot.get("margin_override") not in (None, ""):
            m, src = D(lot["margin_override"]), "лот"
        else:
            key = f"{svc['supplier_id']}:{svc['service_id']}"
            sm = (cfg.get("margins.service") or {}).get(key)
            cm = (cfg.get("margins.category") or {}).get(svc.get("category") or "")
            if sm is not None:
                m, src = D(sm), "услуга"
            elif cm is not None:
                m, src = D(cm), "категория"
            else:
                m, src = cfg.dec("margin_default"), "по умолчанию"
        if lot and lot.get("discount_active") and cfg.get("smart_discount.enabled"):
            mm = cfg.dec("min_margin")
            if mm < m:
                return mm, f"умная скидка (было {m}% — {src})"
        return m, src

    def lot_unit(self, lot: dict) -> int:
        """Сколько единиц услуги в 1 шт. лота FunPay."""
        if to_int(lot.get("pack_qty")) > 0:
            return to_int(lot["pack_qty"])
        if lot.get("template_id"):
            t = self.p.db.one("SELECT price_mode FROM templates WHERE id=?", (lot["template_id"],))
            if t and t["price_mode"] == "per_1":
                return 1
        return max(1, int(self.p.cfg.get("lot_unit")))

    def lot_candidates(self, lot_id: int, usable_only: bool = True) -> list[dict]:
        sql = ("SELECT ls.lot_id, ls.supplier_id, ls.service_id, ls.is_primary, ls.position, s.name, s.category, "
               "s.rate, s.min, s.max, s.refill, s.cancel, s.disabled, sp.name AS supplier_name, sp.enabled AS "
               "supplier_enabled, sp.needs_key, sp.priority, sp.profile_json FROM lot_services ls "
               "LEFT JOIN services s ON s.supplier_id=ls.supplier_id AND s.service_id=ls.service_id "
               "LEFT JOIN suppliers sp ON sp.id=ls.supplier_id WHERE ls.lot_id=? "
               "ORDER BY ls.is_primary DESC, ls.position, sp.priority")
        rows = self.p.db.query(sql, (lot_id,))
        if usable_only:
            rows = [r for r in rows if r["rate"] is not None and not r["disabled"] and r["supplier_enabled"]
                    and not r["needs_key"]]
        return rows

    def candidate_cost(self, cand: dict, qty: int) -> Decimal:
        s = self.p.sup.get(cand["supplier_id"])
        rate_unit = s.rate_unit if s else 1000
        currency = s.currency if s else "USD"
        return self.cost_rub(cand["rate"], rate_unit, qty, currency)

    def calc_lot(self, lot: dict) -> Optional[dict]:
        """Цена лота по базе price_basis. None — нет доступных кандидатов."""
        cands = self.lot_candidates(lot["id"])
        if not cands:
            return None
        unit = self.lot_unit(lot)
        costs = []
        for c in cands:
            try:
                costs.append((self.candidate_cost(c, unit), c))
            except Exception as e:
                log_warn(f"Лот {lot['id']}: не удалось посчитать кандидата {c['supplier_id']}:{c['service_id']}: {e}")
        if not costs:
            return None
        basis = self.p.cfg.get("price_basis")
        if basis == "CHEAPEST":
            cost, cand = min(costs, key=lambda x: x[0])
        elif basis == "SELECTED":
            prim = [x for x in costs if x[1]["is_primary"]]
            cost, cand = prim[0] if prim else costs[0]
        else:
            cost, cand = max(costs, key=lambda x: x[0])
        margin, src = self.margin_for(lot, cand)
        price = self.final_price(cost, margin, unit)
        if lot.get("manual_price") not in (None, ""):
            price = D(lot["manual_price"])
        return {"price": price, "cost": cost.quantize(Decimal("0.0001")), "margin": margin, "margin_src": src,
                "profit": self.profit(price, cost), "unit": unit, "basis": basis, "cand": cand,
                "manual": lot.get("manual_price") not in (None, "")}

    def calc_service(self, sid: int, svc: dict, qty: int, lot: Optional[dict] = None) -> dict:
        """Цена произвольной услуги (для каталога и предпросмотра)."""
        s = self.p.sup.get(sid)
        cost = self.cost_rub(svc["rate"], s.rate_unit if s else 1000, qty, s.currency if s else "USD")
        margin, src = self.margin_for(lot, dict(svc, supplier_id=sid))
        price = self.final_price(cost, margin, qty)
        return {"cost": cost, "price": price, "profit": self.profit(price, cost), "margin": margin,
                "margin_src": src, "unit": qty}

    def explain(self, lot: dict) -> str:
        """Построчный расчёт цены для Telegram."""
        cands = self.lot_candidates(lot["id"])
        if not cands:
            return "Нет доступных услуг-кандидатов."
        f = self.fees()
        unit = self.lot_unit(lot)
        res = self.calc_lot(lot)
        c = res["cand"]
        s = self.p.sup.get(c["supplier_id"])
        fx = self.p.fx.rate(s.currency)
        k = self.k()
        raw = D(c["rate"]) * D(unit) / D(s.rate_unit)
        lines = [
            f"<b>Расчёт цены лота #{lot['id']}</b>",
            f"База: {res['basis']} → {esc(c['supplier_name'])} / {esc(c['service_id'])}",
            f"Количество в 1 шт. лота: {unit}",
            f"Ставка: {c['rate']} {s.currency} за {s.rate_unit}",
            f"rate × qty/unit = {raw.quantize(Decimal('0.0001'))} {s.currency}",
            f"× курс {fx.quantize(Decimal('0.0001'))} × (1 + {f['buffer'] * 100}%) = "
            f"<b>{money(res['cost'])} ₽</b> себестоимость",
            f"Маржа: {res['margin']}% ({esc(res['margin_src'])})",
            f"Комиссии: FP {f['fp'] * 100}%, вывод {f['wd'] * 100}% → k = {k.quantize(Decimal('0.0001'))}",
            f"cost × (1+m) / k + {f['fixed']} = "
            f"{money(res['cost'] * (1 + res['margin'] / 100) / k + f['fixed'])} ₽",
            f"Минимум: cost + {f['min_profit']}/k = {money(res['cost'] + f['min_profit'] / k)} ₽",
            f"Округление вверх до {f['step'] if unit > 1 else min(f['step'], Decimal('0.01'))}",
            f"<b>Цена: {money(res['price'])} ₽</b>" + (" (ручная)" if res["manual"] else ""),
            f"Чистая прибыль: <b>{money(res['profit'])} ₽</b>",
        ]
        if len(cands) > 1:
            lines.append("\nКандидаты:")
            for cand in cands:
                try:
                    lines.append(f" • {esc(cand['supplier_name'])} {esc(cand['service_id'])}: "
                                 f"{money(self.candidate_cost(cand, unit))} ₽")
                except Exception as e:
                    lines.append(f" • {esc(cand['supplier_name'])} {esc(cand['service_id'])}: ошибка {esc(e)}")
        return "\n".join(lines)


class PriceMonitor:
    """Периодический пересчёт цен привязанных лотов."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.last_run = 0

    def _update_discounts(self) -> None:
        if not self.p.cfg.get("smart_discount.enabled"):
            self.p.db.execute("UPDATE lots SET discount_active=0 WHERE discount_active=1")
            return
        border = now_ts() - int(self.p.cfg.get("smart_discount.days")) * 86400
        self.p.db.execute("UPDATE lots SET discount_active=1 WHERE discount_active=0 AND enabled=1 AND "
                          "COALESCE(last_sale_at, created_at) < ?", (border,))
        self.p.db.execute("UPDATE lots SET discount_active=0 WHERE discount_active=1 AND "
                          "COALESCE(last_sale_at, created_at) >= ?", (border,))

    def run_once(self) -> dict:
        """Пересчитывает цены; возвращает счётчики."""
        self.last_run = now_ts()
        self._update_discounts()
        stats = {"checked": 0, "updated": 0, "skipped": 0, "errors": 0}
        respect = self.p.cfg.get("respect_manual_edits")
        threshold = self.p.cfg.dec("price_change_threshold")
        min_profit = self.p.cfg.dec("min_profit_abs")
        lots = self.p.db.query("SELECT * FROM lots WHERE fp_lot_id IS NOT NULL AND enabled=1 AND lost=0 AND "
                               "(manual_price IS NULL OR manual_price='')")
        for lot in lots:
            if self.p.stop.is_set():
                break
            if respect and lot["manual_edit"]:
                stats["skipped"] += 1
                continue
            stats["checked"] += 1
            try:
                res = self.p.price.calc_lot(lot)
                if not res:
                    stats["skipped"] += 1
                    continue
                new = res["price"]
                old = D(lot["price"]) if lot["price"] else Decimal("0")
                reason = None
                if old <= 0:
                    reason = "init"
                else:
                    change = abs(new - old) / old * 100
                    if change > threshold:
                        reason = f"change {change:.1f}%"
                    elif self.p.price.profit(old, res["cost"]) < min_profit:
                        reason = "low_profit"
                if reason and new != old:
                    if self.push_price(lot, new, reason):
                        stats["updated"] += 1
                    else:
                        stats["errors"] += 1
                    time.sleep(float(self.p.cfg.get("fp_pause")))
            except Exception as e:
                stats["errors"] += 1
                log_error(f"PriceMonitor: лот {lot['id']}: {e}", exc=True)
        if stats["updated"] or stats["errors"]:
            log_info(f"PriceMonitor: {stats}")
        return stats

    def push_price(self, lot: dict, new: Decimal, reason: str) -> bool:
        """Обновляет цену лота на FP и пишет price_log."""
        old = lot.get("price")
        if self.p.dry:
            log_info(f"[DRY-RUN] Цена лота {lot['id']} (FP {lot['fp_lot_id']}): {old} -> {new} ({reason})")
            return True
        try:
            self.p.ml.fp_update(int(lot["fp_lot_id"]), {"price": new})
        except Exception as e:
            log_error(f"Не удалось обновить цену лота {lot['fp_lot_id']}: {e}", exc=True)
            return False
        self.p.db.execute("UPDATE lots SET price=?, updated_at=? WHERE id=?", (str(new), now_ts(), lot["id"]))
        self.p.db.execute("INSERT INTO price_log(lot_id, old, new, reason, ts) VALUES(?,?,?,?,?)",
                          (lot["id"], str(old), str(new), reason, now_ts()))
        log_info(f"Цена лота {lot['fp_lot_id']}: {old} -> {new} ({reason})")
        return True


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# F. CATALOG: кэш каталога, сопоставление услуг, рейтинг услуг, автовыбор
# ═══════════════════════════════════════════════════════════════════════════════════════════════

PLATFORMS: list[tuple[str, tuple[str, ...], str]] = [
    ("Instagram", ("instagram", "инстаграм", "insta", " ig "), r"^https://(www\.)?instagram\.com/\S+$"),
    ("TikTok", ("tiktok", "тикток", "tik tok"), r"^https://((www|vm|vt|m)\.)?tiktok\.com/\S+$"),
    ("YouTube", ("youtube", "ютуб", "you tube", "shorts"), r"^https://((www|m)\.)?(youtube\.com|youtu\.be)/\S+$"),
    ("Telegram", ("telegram", "телеграм", "tg ", " тг"), r"^https://(t\.me|telegram\.me)/\S+$"),
    ("VK", ("vk", "вконтакте", "вк "), r"^https://((m|www)\.)?vk\.(com|ru)/\S+$"),
    ("Twitter/X", ("twitter", "твиттер", " x.com", "tweet"), r"^https://((www|mobile)\.)?(twitter\.com|x\.com)/\S+$"),
]


def detect_platform(*texts: Any) -> Optional[tuple[str, str]]:
    """(название, regex) платформы по названию/категории услуги."""
    blob = " " + " ".join(norm_text(t) for t in texts) + " "
    for name, keys, rx in PLATFORMS:
        if any(k in blob for k in keys):
            return name, rx
    return None


def validate_link(link: str, platform: Optional[tuple[str, str]]) -> Optional[str]:
    """None — ссылка валидна, иначе причина."""
    if not link:
        return "пустая ссылка"
    if re.search(r"\s", link):
        return "ссылка содержит пробелы"
    if not link.startswith("https://"):
        return "нужна ссылка, начинающаяся с https://"
    if not re.match(r"^https://[^\s/]+\.[^\s/]+(/\S*)?$", link):
        return "некорректный формат"
    if platform and not re.match(platform[1], link, re.I):
        return f"нужна ссылка {platform[0]}"
    return None


class Catalog:
    """Рейтинг услуг, ETA, автовыбор кандидатов, подсказки."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self._excluded_notified: dict[str, float] = {}

    def stats(self, sid: int, svc: str) -> Optional[dict]:
        return self.p.db.one("SELECT * FROM service_stats WHERE supplier_id=? AND service_id=?", (sid, str(svc)))

    def rating(self, sid: int, svc: str) -> tuple[float, int]:
        st = self.stats(sid, svc)
        if not st:
            return 0.5, 0
        return float(st["rating"] if st["rating"] is not None else 0.5), int(st["orders_total"] or 0)

    def default_eta(self, category: str, name: str = "") -> int:
        eta = self.p.cfg.get("eta_defaults") or {}
        blob = norm_text(f"{category} {name}")
        for key, val in eta.items():
            if key != "default" and key in blob:
                return int(val)
        return int(eta.get("default", 3600))

    def recompute_stats(self, sid: int, svc: str) -> None:
        """Пересчёт service_stats за 50 последних заказов или 30 дней."""
        svc = str(svc)
        border = now_ts() - 30 * 86400
        orders = self.p.db.query(
            "SELECT status, sent_at, completed_at FROM orders WHERE supplier_id=? AND service_id=? AND "
            "status IN ('COMPLETED','PARTIAL','CANCELED','FAILED','REFUNDED','CLOSED') AND "
            "(created_at>=? OR id IN (SELECT id FROM orders WHERE supplier_id=? AND service_id=? "
            "ORDER BY id DESC LIMIT 50)) ORDER BY id DESC LIMIT 50", (sid, svc, border, sid, svc))
        fails = self.p.db.query("SELECT details FROM order_events WHERE event='supplier_fail' AND ts>=?", (border,))
        refills = self.p.db.query("SELECT details FROM order_events WHERE event='refill' AND ts>=?", (border,))
        key = f"{sid}:{svc}"
        n_fail_ev = sum(1 for r in fails if (r["details"] or "").startswith(key + " ") or r["details"] == key)
        n_refill = sum(1 for r in refills if (r["details"] or "").startswith(key))
        completed = sum(1 for o in orders if o["status"] in (ORDER_COMPLETED, ORDER_CLOSED))
        partial = sum(1 for o in orders if o["status"] == ORDER_PARTIAL)
        canceled = sum(1 for o in orders if o["status"] in (ORDER_CANCELED, ORDER_REFUNDED))
        failed = sum(1 for o in orders if o["status"] == ORDER_FAILED) + n_fail_ev
        total = completed + partial + canceled + failed
        durations = [o["completed_at"] - o["sent_at"] for o in orders
                     if o["status"] in (ORDER_COMPLETED, ORDER_CLOSED) and o["sent_at"] and o["completed_at"]]
        med = int(statistics.median(durations)) if durations else None
        if total < 10:
            rating = 0.5
        else:
            svc_row = self.p.sup.service(sid, svc) or {}
            eta_def = self.default_eta(svc_row.get("category", ""), svc_row.get("name", ""))
            speed = max(0.0, min(1.0, 1 - (med / (2 * eta_def)))) if med is not None else 0.5
            rating = (0.5 * completed / total + 0.2 * (1 - partial / total) + 0.2 * (1 - min(1.0, n_refill / total))
                      + 0.1 * speed)
        self.p.db.execute(
            "INSERT INTO service_stats(supplier_id, service_id, orders_total, completed, partial, canceled, failed,"
            " refills, avg_seconds, rating, updated_at) VALUES(?,?,?,?,?,?,?,?,?,?,?)"
            " ON CONFLICT(supplier_id, service_id) DO UPDATE SET orders_total=excluded.orders_total,"
            " completed=excluded.completed, partial=excluded.partial, canceled=excluded.canceled,"
            " failed=excluded.failed, refills=excluded.refills, avg_seconds=excluded.avg_seconds,"
            " rating=excluded.rating, updated_at=excluded.updated_at",
            (sid, svc, total, completed, partial, canceled, failed, n_refill, med, round(rating, 4), now_ts()))

    def eta_seconds(self, sid: Optional[int], svc: Optional[str], category: str = "", name: str = "") -> int:
        """Медиана по 30 последним заказам × 1.2; при < 5 заказах — дефолт категории."""
        if sid and svc:
            rows = self.p.db.query(
                "SELECT completed_at - sent_at AS d FROM orders WHERE supplier_id=? AND service_id=? AND "
                "status IN ('COMPLETED','CLOSED') AND sent_at IS NOT NULL AND completed_at IS NOT NULL "
                "ORDER BY id DESC LIMIT 30", (sid, str(svc)))
            durations = [r["d"] for r in rows if r["d"] is not None and r["d"] >= 0]
            if len(durations) >= 5:
                return int(statistics.median(durations) * 1.2)
        return self.default_eta(category, name)

    def lot_mode(self, lot: dict) -> str:
        if lot.get("mode") in SELECT_MODES:
            return lot["mode"]
        by_cat = self.p.cfg.get("select_mode_by_category") or {}
        m = by_cat.get(str(lot.get("node_id")))
        if m in SELECT_MODES:
            return m
        return self.p.cfg.get("select_mode_default") if self.p.cfg.get("select_mode_default") in SELECT_MODES \
            else "CHEAPEST"

    def _notify_excluded(self, cand: dict, reason: str) -> None:
        key = f"{cand['supplier_id']}:{cand['service_id']}:{reason}"
        if time.time() - self._excluded_notified.get(key, 0) < 3600:
            return
        self._excluded_notified[key] = time.time()
        self.p.alerts.send(f"🚷 Автоисключение кандидата {esc(cand['supplier_name'])} / "
                           f"{esc(cand['service_id'])}: {esc(reason)}", key=f"excl:{key}")

    def select_candidates(self, lot: dict, qty: int, exclude: Optional[set] = None,
                          reasons: Optional[dict] = None) -> list[dict]:
        """Упорядоченный список кандидатов для заказа с учётом режима и исключений.

        reasons (если передан) собирает причины исключения: {код: количество} — для понятного автовозврата.
        """
        exclude = exclude or set()
        reasons = reasons if reasons is not None else {}

        def skip(code: str) -> None:
            reasons[code] = reasons.get(code, 0) + 1

        result = []
        min_rating = float(self.p.cfg.get("min_rating"))
        for c in self.p.price.lot_candidates(lot["id"], usable_only=False):
            key = f"{c['supplier_id']}:{c['service_id']}"
            if key in exclude:
                skip("tried")
                continue
            if not c["supplier_enabled"] or c["needs_key"] or c["supplier_name"] is None:
                skip("no_api")
                continue
            if c["rate"] is None or c["disabled"]:
                skip("service")
                continue
            if not (int(c["min"] or 1) <= qty <= int(c["max"] or 10 ** 9)):
                skip("qty")
                continue
            s = self.p.sup.get(c["supplier_id"])
            if not s or not s.api_key:
                skip("no_api")
                continue
            if s.breaker.is_open:
                skip("api_down")
                self._notify_excluded(c, "circuit breaker")
                continue
            rating, total = self.rating(c["supplier_id"], c["service_id"])
            if total >= 20 and rating < min_rating:
                skip("no_supplier")
                self._notify_excluded(c, f"рейтинг {rating:.2f} < {min_rating}")
                continue
            try:
                cost_rub = self.p.price.candidate_cost(c, qty)
            except Exception as e:
                skip("fx")
                log_warn(f"Кандидат {key}: нет цены ({e})")
                continue
            native = D(c["rate"]) * D(qty) / D(s.rate_unit)
            if not self.p.dry:
                bal, _cur = self.p.sup.balance(c["supplier_id"])
                if bal is None and s.breaker.is_open:
                    skip("api_down")
                    continue
                if bal is not None and bal < native:
                    skip("no_balance")
                    self._notify_excluded(c, f"недостаточно баланса ({money(bal)} < {money(native)} {s.currency})")
                    continue
            result.append(dict(c, cost_rub=cost_rub, cost_native=native, rating=rating, orders_total=total))
        if not result:
            return []
        mode = self.lot_mode(lot)
        if mode == "CHEAPEST":
            result.sort(key=lambda x: (x["cost_rub"], x["priority"] or 100))
        elif mode == "QUALITY":
            result.sort(key=lambda x: (-x["rating"], x["cost_rub"]))
        elif mode == "BALANCED":
            lo = min(x["cost_rub"] for x in result)
            hi = max(x["cost_rub"] for x in result)
            wp, wq = float(self.p.cfg.get("w_price")), float(self.p.cfg.get("w_quality"))
            for x in result:
                norm = float((x["cost_rub"] - lo) / (hi - lo)) if hi > lo else 0.0
                x["score"] = wp * (1 - norm) + wq * x["rating"]
            result.sort(key=lambda x: -x["score"])
        else:
            result.sort(key=lambda x: (-int(x["is_primary"] or 0), int(x["position"] or 0)))
        return result

    def suggest(self, lot: dict, limit: int = 8) -> list[dict]:
        """Подсказки кандидатов по совпадению названия и категории."""
        bound = self.p.price.lot_candidates(lot["id"], usable_only=False)
        if not bound:
            return []
        base = bound[0]
        base_name = norm_text(base["name"])
        base_platform = detect_platform(base["name"], base["category"])
        have = {f"{b['supplier_id']}:{b['service_id']}" for b in bound}
        scored = []
        for sup in self.p.sup.list(enabled_only=True):
            for s in self.p.sup.services(sup["id"], include_disabled=False):
                key = f"{sup['id']}:{s['service_id']}"
                if key in have:
                    continue
                plat = detect_platform(s["name"], s["category"])
                if base_platform and plat and plat[0] != base_platform[0]:
                    continue
                score = difflib.SequenceMatcher(None, base_name, norm_text(s["name"])).ratio()
                score += 0.3 * difflib.SequenceMatcher(None, norm_text(base["category"]),
                                                       norm_text(s["category"])).ratio()
                scored.append((score, dict(s, supplier_name=sup["name"])))
        scored.sort(key=lambda x: -x[0])
        return [dict(x[1], score=round(x[0], 2)) for x in scored[:limit]]

    def top_lots(self, days: int = 7, n: int = 5) -> list[dict]:
        return self.p.db.query(
            "SELECT lot_id, COUNT(*) AS cnt FROM orders WHERE created_at>=? AND lot_id IS NOT NULL "
            "GROUP BY lot_id ORDER BY cnt DESC LIMIT ?", (now_ts() - days * 86400, n))

    def is_top(self, sid: int, svc: str) -> bool:
        n = int(self.p.cfg.get("badge_top_n"))
        rows = self.p.db.query(
            "SELECT supplier_id, service_id, COUNT(*) AS cnt FROM orders WHERE created_at>=? AND service_id IS NOT "
            "NULL GROUP BY supplier_id, service_id ORDER BY cnt DESC LIMIT ?", (now_ts() - 7 * 86400, n))
        return any(r["supplier_id"] == sid and str(r["service_id"]) == str(svc) for r in rows)


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# G. MASTERLOT: шаблоны, кодовые слова, предпросмотр, upsert лотов
# ═══════════════════════════════════════════════════════════════════════════════════════════════

def _yes_no(v: Any) -> str:
    return "да" if to_bool(v) else "нет"


def _parse_start(ctx: dict) -> str:
    m = re.search(r"(?:старт|start)\s*[:\-]?\s*(\d+(?:[.,]\d+)?(?:\s*[-–]\s*\d+(?:[.,]\d+)?)?\s*"
                  r"(?:ч|час[а-я]*|h|hours?|мин[а-я]*|min|m|д|дн[а-я]*|days?)?)", ctx["svc"].get("name", ""), re.I)
    if m:
        return m.group(1).strip()
    if re.search(r"instant|мгновен", ctx["svc"].get("name", ""), re.I):
        return "мгновенно"
    return ctx["p"].cfg.get("default_start_time")


def _parse_speed(ctx: dict) -> str:
    m = re.search(r"(\d+(?:[.,]\d+)?\s*[kк]?)\s*/\s*(day|d|день|д|сутки|час|h|hour)", ctx["svc"].get("name", ""),
                  re.I)
    if not m:
        m2 = re.search(r"(?:скорость|speed)\s*[:\-]?\s*([^,|\]\)\n]{1,25})", ctx["svc"].get("name", ""), re.I)
        return m2.group(1).strip() if m2 else "—"
    return f"{m.group(1).strip()}/{m.group(2)}"


def _parse_guarantee(ctx: dict) -> str:
    name = ctx["svc"].get("name", "")
    m = re.search(r"\bR\s?(\d{1,3})\b", name) or re.search(r"(\d{1,3})\s*(?:дн|day|days|д\.)", name, re.I)
    if m:
        return f"{m.group(1)} дней"
    if re.search(r"lifetime|навсегда|пожизн", name, re.I):
        return "пожизненная"
    return "есть (докрутка)" if to_bool(ctx["svc"].get("refill")) else "нет"


LOT_CODE_RESOLVERS: dict[str, Callable[[dict], str]] = {
    "service_name": lambda ctx: str(ctx["svc"].get("name", "")),
    "category": lambda ctx: str(ctx["svc"].get("category", "")),
    "id": lambda ctx: ctx["marker"],
    "supplier": lambda ctx: str(ctx["supplier"].get("name", "")),
    "min": lambda ctx: str(ctx["svc"].get("min", "")),
    "max": lambda ctx: str(ctx["svc"].get("max", "")),
    "price_per_1k": lambda ctx: money(ctx["price_per_1k"]),
    "quantity": lambda ctx: str(ctx["unit"]),
    "refill": lambda ctx: _yes_no(ctx["svc"].get("refill")),
    "cancel": lambda ctx: _yes_no(ctx["svc"].get("cancel")),
    "start_time": _parse_start,
    "speed": _parse_speed,
    "guarantee": _parse_guarantee,
    "badge": lambda ctx: ctx["p"].cfg.get("badge_text") if ctx["p"].cat.is_top(ctx["supplier"]["id"],
                                                                                ctx["svc"]["service_id"]) else "",
    "platform": lambda ctx: (detect_platform(ctx["svc"].get("name"), ctx["svc"].get("category")) or ("SMM", ""))[0],
}

# Галерея готовых шаблонов: продающие заголовки и описания с кодовыми словами.
_DESC_COMMON = (
    "✅ Автоматический запуск 24/7 — сразу после оплаты пришлите ссылку в чат.\n"
    "⏱ Старт: {start_time} | Скорость: {speed}\n"
    "🛡 Гарантия: {guarantee}\n"
    "📦 Количество: {quantity} шт.\n\n"
    "Как заказать:\n"
    "1. Оплатите лот (можно купить несколько штук — количество умножится).\n"
    "2. Пришлите ссылку одним сообщением (https://...).\n"
    "3. Подтвердите «+» — заказ запустится автоматически.\n\n"
    "⚠️ Профиль/канал должен быть открытым. Не меняйте ссылку и не закрывайте профиль до завершения.\n"
    "Статус заказа можно спросить в чате словом «статус»."
)
_DESC_COMMON_EN = (
    "✅ Fully automatic 24/7 — send your link in chat right after payment.\n"
    "⏱ Start: {start_time} | Speed: {speed}\n"
    "🛡 Guarantee: {guarantee}\n"
    "📦 Quantity: {quantity}\n\n"
    "The profile/channel must be public. Type “status” in chat to check progress."
)
TEMPLATE_PRESETS: dict[str, dict] = {
    "universal": {
        "title": "🌐 Универсальный (любая платформа)",
        "keywords": [],
        "name": "Универсальный SMM",
        "title_ru": "{badge} {platform} — {service_name} | {quantity} шт. | Автозапуск",
        "title_en": "{platform} — {service_name} | {quantity} pcs | Auto start",
        "desc_ru": "🚀 {service_name}\n\n" + _DESC_COMMON,
        "desc_en": "🚀 {service_name}\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "ig_followers": {
        "node_hints": ["подписч"],
        "title": "📸 Instagram — подписчики",
        "keywords": ["instagram", "инстаграм"],
        "name": "Instagram подписчики",
        "title_ru": "{badge} Подписчики Instagram {quantity} шт. ⚡ Старт {start_time} 🛡 Гарантия {guarantee}",
        "title_en": "Instagram Followers {quantity} ⚡ Start {start_time} 🛡 Refill {guarantee}",
        "desc_ru": "👥 Подписчики в Instagram — {service_name}\n\n" + _DESC_COMMON +
                   "\n\nПришлите ссылку на профиль: https://instagram.com/username",
        "desc_en": "👥 Instagram followers\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "ig_likes": {
        "node_hints": ["лайк"],
        "title": "❤️ Instagram — лайки / просмотры",
        "keywords": ["instagram", "инстаграм"],
        "name": "Instagram лайки",
        "title_ru": "{badge} Лайки Instagram {quantity} шт. ⚡ Быстрый старт | Автовыдача",
        "title_en": "Instagram Likes {quantity} ⚡ Fast start | Auto",
        "desc_ru": "❤️ {service_name}\n\n" + _DESC_COMMON + "\n\nПришлите ссылку на пост/рилс.",
        "desc_en": "❤️ Instagram likes\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "tiktok": {
        "node_hints": ["просмотр", "подписч"],
        "title": "🎵 TikTok — просмотры / подписчики / лайки",
        "keywords": ["tiktok", "тикток"],
        "name": "TikTok",
        "title_ru": "{badge} TikTok {service_name} — {quantity} шт. ⚡ Автозапуск",
        "title_en": "TikTok {service_name} — {quantity} ⚡ Auto start",
        "desc_ru": "🎵 {service_name}\n\n" + _DESC_COMMON + "\n\nПришлите ссылку на видео или профиль TikTok.",
        "desc_en": "🎵 TikTok\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "youtube": {
        "node_hints": ["просмотр", "подписч"],
        "title": "▶️ YouTube — просмотры / подписчики",
        "keywords": ["youtube", "ютуб"],
        "name": "YouTube",
        "title_ru": "{badge} YouTube {service_name} — {quantity} шт. 🛡 {guarantee}",
        "title_en": "YouTube {service_name} — {quantity} 🛡 {guarantee}",
        "desc_ru": "▶️ {service_name}\n\n" + _DESC_COMMON + "\n\nПришлите ссылку на видео или канал YouTube.",
        "desc_en": "▶️ YouTube\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "telegram": {
        "node_hints": ["подписч", "участник"],
        "title": "✈️ Telegram — подписчики / просмотры",
        "keywords": ["telegram", "телеграм"],
        "name": "Telegram",
        "title_ru": "{badge} Telegram {service_name} — {quantity} шт. ⚡ Старт {start_time}",
        "title_en": "Telegram {service_name} — {quantity} ⚡ Start {start_time}",
        "desc_ru": "✈️ {service_name}\n\n" + _DESC_COMMON +
                   "\n\nПришлите ссылку на публичный канал/пост: https://t.me/channel",
        "desc_en": "✈️ Telegram\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "vk": {
        "node_hints": ["подписч", "лайк"],
        "title": "🔵 VK — подписчики / лайки",
        "keywords": ["вконтакте", "vk"],
        "name": "VK",
        "title_ru": "{badge} ВКонтакте {service_name} — {quantity} шт. | Автозапуск",
        "title_en": "VK {service_name} — {quantity} | Auto",
        "desc_ru": "🔵 {service_name}\n\n" + _DESC_COMMON + "\n\nПришлите ссылку на страницу/группу/пост VK.",
        "desc_en": "🔵 VK\n\n" + _DESC_COMMON_EN,
        "price_mode": "per_1000",
    },
    "packs": {
        "title": "📦 Пакеты (100 / 500 / 1000 / 5000)",
        "keywords": [],
        "name": "Пакеты",
        "title_ru": "{badge} {platform} {service_name} — пакет {quantity} шт.",
        "title_en": "{platform} {service_name} — {quantity} pack",
        "desc_ru": "📦 Пакет {quantity} шт. — {service_name}\n\n" + _DESC_COMMON,
        "desc_en": "📦 {quantity} pack\n\n" + _DESC_COMMON_EN,
        "price_mode": "pack",
        "quantity_pack": "100, 500, 1000, 5000",
    },
}
for _p in TEMPLATE_PRESETS.values():
    _p.setdefault("secrets_text", "")
    _p.setdefault("quantity_pack", "")
    _p.setdefault("autoreply_text", "Заказ #{order_id} запущен 🚀 Ожидаемое время: {eta}. Напишите «статус», "
                                    "чтобы узнать прогресс.")

# Синонимы для поиска категорий FunPay (кириллица/латиница/сленг).
SEARCH_SYNONYMS = {
    "тикток": ["tiktok", "тикток"], "tiktok": ["tiktok", "тикток"], "тик": ["tiktok", "тикток"],
    "инстаграм": ["instagram", "инстаграм"], "инста": ["instagram", "инстаграм"], "insta": ["instagram"],
    "instagram": ["instagram", "инстаграм"], "ютуб": ["youtube", "ютуб"], "youtube": ["youtube", "ютуб"],
    "телеграм": ["telegram", "телеграм"], "тг": ["telegram", "телеграм"], "telegram": ["telegram", "телеграм"],
    "вк": ["вконтакте", "vk"], "вконтакте": ["вконтакте", "vk"], "vk": ["vk", "вконтакте"],
    "твиттер": ["twitter", "твиттер", " x "], "twitter": ["twitter", "твиттер"],
    "подписчики": ["подписч", "follow", "subscri", "участник", "member"],
    "лайки": ["лайк", "like", "реакц"], "просмотры": ["просмотр", "view"],
}

TEMPLATE_STEP_TIPS = {
    "name": "Название видно только вам. Пример: «Instagram подписчики R30».",
    "title_ru": "💡 Советы: начинайте с платформы и типа услуги (по ним ищут на FunPay), добавьте {quantity}, "
                "гарантию {guarantee} и старт {start_time}. Держите до 100 символов — длиннее обрежется "
                "автоматически.",
    "title_en": "💡 Для англоязычных покупателей. «-» — скопировать русский.",
    "desc_ru": "💡 Хорошее описание: что получит покупатель, сроки ({start_time}, {speed}), гарантия ({guarantee}), "
               "инструкция «оплатите → пришлите ссылку → «+»», требование открытого профиля.",
    "desc_en": "💡 Можно коротко. «-» — оставить пустым.",
    "category_node": "💡 Можно ввести ID числом или просто текст: «instagram», «tiktok подписчики» — плагин найдёт "
                     "подкатегории FunPay и покажет кнопки.",
    "price_mode": "💡 «За 1000» — покупатель берёт N шт. лота = N×1000. «Пакеты» — отдельный лот на каждый объём. "
                  "«За 1 шт.» — покупатель сам выбирает точное количество.",
    "quantity_pack": "💡 Популярные объёмы продаются лучше: 100, 500, 1000, 5000.",
    "secrets_text": "💡 Сообщение сразу после оплаты (например, инструкция). «-» — не отправлять.",
    "autoreply_text": "💡 Отправляется при запуске заказа. Доступны {order_id} {eta} {quantity} {link}. «-» — без него.",
}


CODE_WORD_RX = re.compile(r"\{([a-zA-Z_][a-zA-Z0-9_]*)\}")


def render_codewords(text: str, resolvers: dict[str, Callable[[dict], str]], ctx: dict) -> tuple[str, set]:
    """Подставляет кодовые слова; неизвестные остаются как есть и возвращаются во множестве."""
    unknown: set = set()

    def repl(m: re.Match) -> str:
        key = m.group(1)
        fn = resolvers.get(key)
        if not fn:
            unknown.add(key)
            return m.group(0)
        try:
            return str(fn(ctx))
        except Exception as e:
            log_warn(f"Кодовое слово {{{key}}}: {e}")
            return ""

    return CODE_WORD_RX.sub(repl, text or ""), unknown


class MasterLot:
    """Шаблоны лотов, генерация, предпросмотр, upsert на FunPay."""

    TEMPLATE_FIELDS = ("name", "title_ru", "title_en", "desc_ru", "desc_en", "category_node", "price_mode",
                       "quantity_pack", "secrets_text", "autoreply_text")

    def __init__(self, p: "AutoSMM"):
        self.p = p

    # ── шаблоны ──
    def template(self, tid: int) -> Optional[dict]:
        return self.p.db.one("SELECT * FROM templates WHERE id=?", (tid,))

    def templates(self) -> list[dict]:
        return self.p.db.query("SELECT * FROM templates ORDER BY id")

    def save_template(self, data: dict, tid: Optional[int] = None) -> int:
        fields = {k: data.get(k) for k in self.TEMPLATE_FIELDS if k in data}
        if tid:
            sets = ", ".join(f"{k}=?" for k in fields)
            self.p.db.execute(f"UPDATE templates SET {sets} WHERE id=?", list(fields.values()) + [tid])
            return tid
        fields["created_at"] = now_ts()
        cols = ", ".join(fields)
        return self.p.db.execute(f"INSERT INTO templates({cols}) VALUES({','.join('?' * len(fields))})",
                                 list(fields.values()))

    def delete_template(self, tid: int) -> None:
        self.p.db.execute("UPDATE lots SET template_id=NULL WHERE template_id=?", (tid,))
        self.p.db.execute("DELETE FROM templates WHERE id=?", (tid,))

    @staticmethod
    def packs(template: dict) -> list[int]:
        if template.get("price_mode") != "pack":
            return [0]
        packs = sorted({int(x) for x in re.findall(r"\d+", template.get("quantity_pack") or "") if int(x) > 0})
        return packs or [1000]

    # ── генерация ──
    @staticmethod
    def marker(sid: int, svc: str, pack: int = 0) -> str:
        return f"ASM-{sid}-{svc}" + (f"-{pack}" if pack else "")

    def unit_for(self, template: dict, pack: int) -> int:
        if pack:
            return pack
        if template.get("price_mode") == "per_1":
            return 1
        return max(1, int(self.p.cfg.get("lot_unit")))

    @staticmethod
    def trim_title(text: str, limit: int) -> str:
        """Обрезает заголовок по границе слова, не ломая смысл."""
        if limit <= 0 or len(text) <= limit:
            return text
        cut = text[:limit + 1].rsplit(" ", 1)[0].rstrip(" ,.;:-—|/")
        return cut if len(cut) >= limit * 0.6 else text[:limit].rstrip()

    def build(self, template: dict, sid: int, svc: dict, pack: int = 0, lot: Optional[dict] = None,
              margin: Optional[Decimal] = None) -> dict:
        """Готовые поля лота: заголовки, описания, цена, расчёт, предупреждения.

        margin — наценка, выбранная при запуске мастер-лота (сохраняется в лот как margin_override).
        """
        supplier = self.p.sup.row(sid) or {"id": sid, "name": f"#{sid}"}
        unit = self.unit_for(template, pack)
        eff = lot
        if margin is not None:
            eff = dict(lot or {}, margin_override=str(margin))
        calc = None
        if lot:
            calc = self.p.price.calc_lot(eff)
        if not calc:
            calc = self.p.price.calc_service(sid, svc, unit, eff)
        per_1k = self.p.price.calc_service(sid, svc, 1000, eff)["price"]
        ctx = {"p": self.p, "svc": dict(svc), "supplier": supplier, "template": template, "unit": unit,
               "price_per_1k": per_1k, "marker": self.marker(sid, svc["service_id"], pack)}
        unknown: set = set()
        out = {}
        for key, src in (("title_ru", "title_ru"), ("title_en", "title_en"), ("desc_ru", "desc_ru"),
                         ("desc_en", "desc_en"), ("autoreply", "autoreply_text"), ("secrets", "secrets_text")):
            text, unk = render_codewords(template.get(src) or "", LOT_CODE_RESOLVERS, ctx)
            if key in ("autoreply", "secrets"):
                unk -= set(MESSAGE_CODE_WORDS_HELP)
            unknown |= unk
            out[key] = re.sub(r"[ \t]+", " ", text).strip()
        if not out["title_en"]:
            out["title_en"] = out["title_ru"]
        limit = int(self.p.cfg.get("masterlot.title_limit"))
        warns: list[str] = []
        for key in ("title_ru", "title_en"):
            trimmed = self.trim_title(out[key], limit)
            if trimmed != out[key]:
                out[key] = trimmed
                if key == "title_ru":
                    warns.append(f"заголовок обрезан до {limit} символов")
        if self.p.cfg.get("desc_marker") and "{id}" not in (template.get("desc_ru") or ""):
            out["desc_ru"] = (out["desc_ru"] + f"\n\n{ctx['marker']}").strip()
            if out["desc_en"]:
                out["desc_en"] = (out["desc_en"] + f"\n\n{ctx['marker']}").strip()
        skip = None
        if calc["price"] < D(self.p.cfg.get("masterlot.min_price")):
            skip = f"цена {money(calc['price'])} ₽ ниже минимальной"
        elif calc["profit"] <= 0 and self.p.cfg.get("masterlot.skip_unprofitable"):
            skip = f"убыточно (прибыль {money(calc['profit'])} ₽)"
        out.update({"price": calc["price"], "cost": calc["cost"], "profit": calc["profit"], "unit": unit,
                    "margin": calc["margin"], "unknown": unknown, "marker": ctx["marker"], "warns": warns,
                    "skip": skip})
        return out

    def select_services(self, sid: int, mode: str, arg: Any) -> list[dict]:
        """mode: cat (arg — категория), sel (arg — список id), flt (arg — (текст, мин, макс) цена за 1000 ₽)."""
        if mode == "cat":
            return self.p.sup.services(sid, category=arg, include_disabled=False)
        if mode == "sel":
            ids = [str(x) for x in arg]
            return [s for s in (self.p.sup.service(sid, i) for i in ids) if s and not s["disabled"]]
        text, lo, hi = arg
        result = []
        for s in self.p.sup.services(sid, text=text or None, include_disabled=False):
            if text and text.lower() not in s["name"].lower():
                continue
            try:
                p1k = self.p.price.calc_service(sid, s, 1000)["price"]
            except Exception:
                continue
            if (lo is None or p1k >= D(lo)) and (hi is None or p1k <= D(hi)):
                result.append(s)
        return result

    def recommend(self, sid: int, category: str, tid: int, n: int = 5) -> list[dict]:
        """Авто-подбор лучших услуг категории с объяснением выбора."""
        t = self.template(tid) or {}
        unit = self.packs(t)[0] or self.unit_for(t, 0)
        items = [s for s in self.p.sup.services(sid, category=category, include_disabled=False)
                 if int(s["min"] or 1) <= unit <= int(s["max"] or 10 ** 9)]
        if not items:
            return []
        picks: dict[str, dict] = {}

        def add(svc: Optional[dict], why: str) -> None:
            if svc and svc["service_id"] not in picks and len(picks) < n:
                picks[svc["service_id"]] = dict(svc, why=why)

        def guarantee_days(s: dict) -> int:
            m = re.search(r"\bR\s?(\d{1,3})\b", s["name"]) or re.search(r"(\d{1,3})\s*(?:дн|day)", s["name"], re.I)
            return int(m.group(1)) if m else (365 if re.search(r"lifetime|навсегда", s["name"], re.I) else 0)

        by_price = sorted(items, key=lambda s: D(s["rate"]))
        refill = [s for s in by_price if to_bool(s["refill"])]
        rated = []
        for s in items:
            rating, total = self.p.cat.rating(sid, s["service_id"])
            if total >= 10:
                rated.append((rating, s))
        add(by_price[0], "самая дешёвая — максимум продаж за счёт цены")
        add(refill[0] if refill else None, "самая дешёвая с гарантией докрутки — меньше жалоб")
        if rated:
            best = max(rated, key=lambda x: x[0])
            add(best[1], f"лучший рейтинг по вашим заказам ({best[0]:.2f})")
        longest = max(items, key=lambda s: (guarantee_days(s), -D(s["rate"])))
        if guarantee_days(longest):
            add(longest, f"самая долгая гарантия ({guarantee_days(longest)} дн.) — премиум-лот")
        add(by_price[len(by_price) // 2], "средняя цена — баланс цены и качества")
        for s in by_price:
            add(s, "следующая по цене")
        return list(picks.values())

    def items(self, template: dict, services: list[dict]) -> list[tuple[dict, int]]:
        result = []
        for s in services:
            for pack in self.packs(template):
                if pack and not (int(s["min"] or 1) <= pack <= int(s["max"] or 10 ** 9)):
                    continue
                result.append((s, pack))
        return result

    def preview(self, tid: int, sid: int, services: list[dict], n: int = 3, margin: Optional[Decimal] = None) -> str:
        """Предпросмотр первых n лотов + сводка по всей пачке (новые/обновления/пропуски, прибыль)."""
        t = self.template(tid)
        if not t:
            return "Шаблон не найден."
        items = self.items(t, services)
        margin_txt = f"{margin}% (выбрана при запуске)" if margin is not None else \
            f"по умолчанию/категории ({self.p.cfg.get('margin_default')}%)"
        lines = [f"<b>Предпросмотр</b> — шаблон «{esc(t['name'])}», лотов к обработке: {len(items)}",
                 f"Наценка: <b>{esc(margin_txt)}</b> — чистыми сверх себестоимости, комиссии FP/вывода уже учтены."]
        unknown: set = set()
        stats = {"new": 0, "upd": 0, "skip": 0, "profit": Decimal("0"), "warn": 0}
        skipped: list[str] = []
        for i, (s, pack) in enumerate(items):
            existing = self.find_lot(tid, sid, s["service_id"], pack)
            try:
                b = self.build(t, sid, s, pack, existing, margin)
            except Exception as e:
                if i < n:
                    lines.append(f"\n❌ {esc(s['service_id'])}: {esc(e)}")
                continue
            unknown |= b["unknown"]
            if b["skip"]:
                stats["skip"] += 1
                skipped.append(f"{s['service_id']}: {b['skip']}")
                continue
            stats["upd" if existing else "new"] += 1
            stats["profit"] += b["profit"]
            stats["warn"] += 1 if b["warns"] else 0
            if i < n:
                warn = ("\n⚠️ " + "; ".join(b["warns"])) if b["warns"] else ""
                lines.append(f"\n<b>{esc(b['title_ru'][:150])}</b>\n{esc(b['desc_ru'][:300])}\n"
                             f"Цена: <b>{money(b['price'])} ₽</b> за {b['unit']} | себестоимость {money(b['cost'])} ₽ | "
                             f"прибыль {money(b['profit'])} ₽ | {'обновление' if existing else 'новый'}{warn}")
        lines.append(f"\n<b>Итого:</b> новых {stats['new']}, обновлений {stats['upd']}, будет пропущено "
                     f"{stats['skip']}. Средняя прибыль с продажи: "
                     f"{money(stats['profit'] / max(1, stats['new'] + stats['upd']))} ₽")
        if stats["warn"]:
            lines.append(f"✂️ Заголовков будет обрезано: {stats['warn']} (лимит "
                         f"{self.p.cfg.get('masterlot.title_limit')} симв.)")
        if skipped:
            lines.append("Пропуски: " + esc("; ".join(skipped[:5])) + (" …" if len(skipped) > 5 else ""))
        if unknown:
            lines.append("\n⚠️ Неизвестные кодовые слова: " + ", ".join("{" + esc(u) + "}" for u in sorted(unknown)))
        if self.p.dry:
            lines.append("\n🧪 Dry-run: на FunPay ничего не отправится.")
        return "\n".join(lines)

    def find_lot(self, tid: int, sid: int, svc: str, pack: int) -> Optional[dict]:
        return self.p.db.one("SELECT * FROM lots WHERE template_id=? AND supplier_id=? AND service_id=? AND "
                             "pack_qty=?", (tid, sid, str(svc), pack))

    def run(self, tid: int, sid: int, services: list[dict],
            progress: Optional[Callable[[int, int, dict], None]] = None, margin: Optional[Decimal] = None) -> dict:
        """Публикация/обновление пачки лотов; ошибка одного лота не останавливает пачку."""
        t = self.template(tid)
        report = {"created": 0, "updated": 0, "skipped": 0, "errors": [], "unknown": set(), "total": 0}
        if not t:
            report["errors"].append("шаблон не найден")
            return report
        items = self.items(t, services)
        report["total"] = len(items)
        for i, (s, pack) in enumerate(items, 1):
            if self.p.stop.is_set():
                break
            try:
                res, _lot_id, info = self.upsert(t, sid, s, pack, margin)
                report[res] += 1
                if info.get("reason") and res == "skipped" and info["reason"] != "без изменений":
                    report["errors"].append(f"{s['service_id']}: пропущен — {info['reason']}")
                report["unknown"] |= info.get("unknown", set())
                if res != "skipped":
                    time.sleep(float(self.p.cfg.get("fp_pause")))
            except Exception as e:
                report["errors"].append(f"{s['service_id']}{'/' + str(pack) if pack else ''}: {str(e)[:150]}")
                log_error(f"MasterLot: {s['service_id']}: {e}", exc=True)
                time.sleep(float(self.p.cfg.get("fp_pause")))
            if progress:
                try:
                    progress(i, len(items), report)
                except Exception:
                    pass
        return report

    def upsert(self, template: dict, sid: int, svc: dict, pack: int = 0,
               margin: Optional[Decimal] = None) -> tuple[str, Optional[int], dict]:
        """Ключ лота = (template_id, supplier_id, service_id[, pack]). Обновляет только разницу."""
        lot = self.find_lot(template["id"], sid, svc["service_id"], pack)
        b = self.build(template, sid, svc, pack, lot, margin)
        info = {"unknown": b["unknown"]}
        if b["skip"]:
            return "skipped", lot["id"] if lot else None, dict(info, reason=b["skip"])
        if margin is not None and lot and not self.p.dry:
            self.p.db.execute("UPDATE lots SET margin_override=? WHERE id=?", (str(margin), lot["id"]))
        fields = {"title_ru": b["title_ru"], "title_en": b["title_en"], "desc_ru": b["desc_ru"],
                  "desc_en": b["desc_en"], "price": b["price"]}
        node = int(template.get("category_node") or 0)
        if lot and lot["fp_lot_id"] and not lot["lost"]:
            if self.p.cfg.get("respect_manual_edits") and lot["manual_edit"]:
                return "skipped", lot["id"], dict(info, reason="ручные правки")
            if lot["manual_price"] not in (None, ""):
                fields.pop("price")
            if self.p.dry:
                log_info(f"[DRY-RUN] Обновление лота FP {lot['fp_lot_id']}: {b['title_ru'][:60]}")
                return "updated", lot["id"], info
            changed = self.fp_update(int(lot["fp_lot_id"]), fields)
            self.p.db.execute("UPDATE lots SET title=?, description=?, price=COALESCE(?, price), updated_at=? "
                              "WHERE id=?", (b["title_ru"], b["desc_ru"],
                                             str(b["price"]) if "price" in fields else None, now_ts(), lot["id"]))
            self._ensure_candidate(lot["id"], sid, svc["service_id"])
            if not changed:
                return "skipped", lot["id"], dict(info, reason="без изменений")
            log_info(f"Лот FP {lot['fp_lot_id']} обновлён: {', '.join(changed)}")
            return "updated", lot["id"], info
        if not node:
            raise ValueError("в шаблоне не указана категория FunPay (node)")
        if self.p.dry:
            log_info(f"[DRY-RUN] Создание лота в node {node}: {b['title_ru'][:60]} цена {b['price']}")
            return "created", lot["id"] if lot else None, info
        fp_id = self.fp_create(node, fields)
        ts = now_ts()
        if lot:
            self.p.db.execute("UPDATE lots SET fp_lot_id=?, node_id=?, title=?, description=?, price=?, lost=0, "
                              "updated_at=? WHERE id=?", (fp_id, node, b["title_ru"], b["desc_ru"], str(b["price"]),
                                                          ts, lot["id"]))
            lot_id = lot["id"]
        else:
            lot_id = self.p.db.execute(
                "INSERT INTO lots(fp_lot_id, node_id, template_id, title, mode, enabled, lost, created_at, updated_at,"
                " pack_qty, supplier_id, service_id, price, description) VALUES(?,?,?,?,NULL,1,0,?,?,?,?,?,?,?)",
                (fp_id, node, template["id"], b["title_ru"], ts, ts, pack, sid, str(svc["service_id"]),
                 str(b["price"]), b["desc_ru"]))
        self._ensure_candidate(lot_id, sid, svc["service_id"], primary=True)
        if margin is not None:
            self.p.db.execute("UPDATE lots SET margin_override=? WHERE id=?", (str(margin), lot_id))
        if self.p.cfg.get("auto.auto_alternatives"):
            try:
                self.p.auto.attach_alternatives(self.p.db.one("SELECT * FROM lots WHERE id=?", (lot_id,)))
            except Exception:
                log_error("Автоподбор запасных поставщиков", exc=True)
        log_info(f"Создан лот FP {fp_id}: {b['title_ru'][:60]}")
        return "created", lot_id, info

    def _ensure_candidate(self, lot_id: int, sid: int, svc: str, primary: bool = False) -> None:
        exists = self.p.db.one("SELECT 1 FROM lot_services WHERE lot_id=? AND supplier_id=? AND service_id=?",
                               (lot_id, sid, str(svc)))
        if exists:
            return
        pos = int(self.p.db.scalar("SELECT COALESCE(MAX(position), -1) + 1 FROM lot_services WHERE lot_id=?",
                                   (lot_id,), 0))
        has_primary = self.p.db.scalar("SELECT 1 FROM lot_services WHERE lot_id=? AND is_primary=1", (lot_id,))
        self.p.db.execute("INSERT INTO lot_services(lot_id, supplier_id, service_id, is_primary, position) "
                          "VALUES(?,?,?,?,?)", (lot_id, sid, str(svc), 1 if primary or not has_primary else 0, pos))

    # ── вызовы FunPay ──
    def fp_create(self, node: int, fields: dict) -> int:
        """Создаёт лот через get_lot_fields(0, node) + save_lot, затем находит его ID в списке лотов подкатегории."""
        c = self.p.c
        with self.p.fp_lock:
            before = {int(x.id) for x in c.account.get_my_subcategory_lots(node)}
            lot_fields = c.account.get_lot_fields(0, node)
            lot_fields.title_ru = fields["title_ru"]
            lot_fields.title_en = fields.get("title_en") or fields["title_ru"]
            lot_fields.description_ru = fields.get("desc_ru", "")
            lot_fields.description_en = fields.get("desc_en", "")
            lot_fields.price = float(fields["price"])
            lot_fields.active = True
            if "amount" in lot_fields.fields:
                lot_fields.amount = int(self.p.cfg.get("lot_stock"))
            c.account.save_lot(lot_fields)
            time.sleep(1)
            # TODO: подтвердить метод Cardinal — save_lot не возвращает ID нового лота,
            # поэтому ID ищется среди новых лотов подкатегории по заголовку.
            after = c.account.get_my_subcategory_lots(node)
        titles = {norm_text(fields["title_ru"]), norm_text(fields.get("title_en") or fields["title_ru"])}
        new = [x for x in after if int(x.id) not in before]
        for x in new:
            if norm_text(x.description) in titles:
                return int(x.id)
        if len(new) == 1:
            return int(new[0].id)
        for x in after:
            if norm_text(x.description) in titles:
                return int(x.id)
        raise RuntimeError("лот сохранён, но его ID не найден в списке лотов подкатегории")

    def fp_update(self, fp_lot_id: int, fields: dict) -> list[str]:
        """Обновляет только изменившиеся поля лота. Возвращает список изменённых полей."""
        c = self.p.c
        with self.p.fp_lock:
            lf = c.account.get_lot_fields(fp_lot_id)
            changed = []
            mapping = (("title_ru", "title_ru"), ("title_en", "title_en"), ("desc_ru", "description_ru"),
                       ("desc_en", "description_en"))
            for key, attr in mapping:
                if key in fields and fields[key] is not None and \
                        (getattr(lf, attr) or "").strip() != str(fields[key]).strip():
                    setattr(lf, attr, str(fields[key]))
                    changed.append(key)
            if "price" in fields and fields["price"] is not None:
                if lf.price is None or abs(D(lf.price) - D(fields["price"])) >= Decimal("0.01"):
                    lf.price = float(fields["price"])
                    changed.append("price")
            if "active" in fields and bool(fields["active"]) != bool(lf.active):
                lf.active = bool(fields["active"])
                changed.append("active")
            if changed:
                c.account.save_lot(lf)
            return changed

    def fp_delete(self, fp_lot_id: int) -> None:
        with self.p.fp_lock:
            self.p.c.account.delete_lot(fp_lot_id)

    def restore_lot(self, lot_id: int) -> str:
        """Пересоздаёт потерянный лот по шаблону (новый fp_lot_id)."""
        lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (lot_id,))
        if not lot:
            return "Лот не найден."
        t = self.template(lot["template_id"]) if lot["template_id"] else None
        svc = self.p.sup.service(lot["supplier_id"], lot["service_id"]) if lot["supplier_id"] else None
        if not t or not svc:
            return "Восстановление возможно только для лотов, созданных мастер-лотом (нужны шаблон и услуга)."
        self.p.db.execute("UPDATE lots SET lost=1, fp_lot_id=NULL WHERE id=?", (lot_id,))
        res, _lid, _info = self.upsert(t, lot["supplier_id"], svc, int(lot["pack_qty"] or 0))
        return f"Результат: {res}."

    def bind_fp_lot(self, fp_lot_id: int, sid: int, svc: str) -> int:
        """Привязывает существующий лот FunPay к услуге (без шаблона)."""
        existing = self.p.db.one("SELECT * FROM lots WHERE fp_lot_id=?", (fp_lot_id,))
        if existing:
            self._ensure_candidate(existing["id"], sid, svc)
            return existing["id"]
        with self.p.fp_lock:
            lf = self.p.c.account.get_lot_fields(fp_lot_id)
        node = lf.subcategory.id if lf.subcategory else None
        ts = now_ts()
        lot_id = self.p.db.execute(
            "INSERT INTO lots(fp_lot_id, node_id, template_id, title, enabled, lost, created_at, updated_at, pack_qty,"
            " supplier_id, service_id, price, description) VALUES(?,?,NULL,?,1,0,?,?,0,?,?,?,?)",
            (fp_lot_id, node, lf.title_ru, ts, ts, sid, str(svc), str(lf.price or ""), lf.description_ru))
        self._ensure_candidate(lot_id, sid, svc, primary=True)
        return lot_id


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# I. MESSAGING: автоответы, ETA, шаблоны
# ═══════════════════════════════════════════════════════════════════════════════════════════════

class Messenger:
    """Сообщения покупателям (случайный вариант из 2-3, тексты в Config)."""

    def __init__(self, p: "AutoSMM"):
        self.p = p

    def variants(self, key: str) -> list[str]:
        v = (self.p.cfg.get("messages") or {}).get(key) or DEFAULTS["messages"].get(key) or [""]
        return [x for x in v if x] or [""]

    @staticmethod
    def render(text: str, values: dict) -> str:
        resolvers = {k: (lambda ctx, _k=k: ctx[_k]) for k in MESSAGE_CODE_WORDS_HELP}
        rendered, _unknown = render_codewords(text, resolvers, {k: str(values.get(k, "")) for k in
                                                                MESSAGE_CODE_WORDS_HELP})
        return rendered

    def order_values(self, order: dict, extra: Optional[dict] = None) -> dict:
        svc = self.p.sup.service(order["supplier_id"], order["service_id"]) if order.get("supplier_id") else None
        if not svc and order.get("lot_id"):
            cands = self.p.price.lot_candidates(order["lot_id"], usable_only=False)
            svc = cands[0] if cands else None
        qty = int(order.get("quantity") or 0)
        remain = order.get("remain")
        done = qty - int(remain) if remain is not None else None
        progress = f"{max(0, done)}/{qty}" if done is not None else "—"
        values = {"order_id": order.get("fp_order_id", ""), "buyer": order.get("buyer", ""),
                  "service_name": (svc or {}).get("name", "услуга"), "quantity": qty,
                  "link": order.get("link") or "—", "eta": order.get("eta_text") or "—",
                  "status": self.status_text(order), "remain": remain if remain is not None else "—",
                  "progress": progress}
        values.update(extra or {})
        return values

    @staticmethod
    def status_text(order: dict) -> str:
        return {ORDER_NEW: "в очереди", ORDER_WAIT_LINK: "ожидает ссылку", ORDER_WAIT_CONFIRM: "ожидает подтверждения",
                ORDER_SENDING: "запускается", ORDER_IN_PROGRESS: "выполняется", ORDER_COMPLETED: "выполнен",
                ORDER_PARTIAL: "выполнен частично", ORDER_CANCELED: "отменён", ORDER_FAILED: "ошибка",
                ORDER_REFUNDED: "возврат", ORDER_CLOSED: "закрыт", ORDER_UNCERTAIN: "проверяется",
                ORDER_REFUND_PENDING: "оформляется возврат"}.get(order.get("status"), str(order.get("status")))

    def send_raw(self, chat_id: Any, buyer: str, text: str) -> bool:
        if not text or chat_id in (None, ""):
            return False
        if self.p.dry:
            log_info(f"[DRY-RUN] Сообщение в чат {chat_id} ({buyer}): {text[:120]!r}")
            return True
        try:
            result = self.p.c.send_message(chat_id, text, buyer)
            return bool(result)
        except Exception:
            log_error(f"Не удалось отправить сообщение в чат {chat_id}", exc=True)
            return False

    def send(self, order: dict, key: str, extra: Optional[dict] = None) -> bool:
        """Отправляет случайный вариант сообщения key по заказу."""
        text = self.render(random.choice(self.variants(key)), self.order_values(order, extra))
        return self.send_raw(order.get("chat_id"), order.get("buyer") or "", text)


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# H. ORDERS: конечный автомат, очередь, воркер статусов, возвраты, fallback
# ═══════════════════════════════════════════════════════════════════════════════════════════════

URL_RX = re.compile(r"https?://\S+", re.I)
PROMO_RX = re.compile(r"\bASM-[A-Z0-9]{6}\b")
TRANSIENT_CODES = ("network", "timeout", "circuit_open", "bad_json") + tuple(f"http_{x}" for x in (429, 500, 502, 503,
                                                                                                  504, 520, 522))


class OrderManager:
    """Заказы: NEW → WAIT_LINK → WAIT_CONFIRM → SENDING → IN_PROGRESS → COMPLETED|PARTIAL|CANCELED|FAILED|REFUNDED."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.lock = threading.RLock()

    # ── доступ к данным ──
    def get(self, oid: int) -> Optional[dict]:
        return self.p.db.one("SELECT * FROM orders WHERE id=?", (oid,))

    def by_fp(self, fp_order_id: str) -> Optional[dict]:
        return self.p.db.one("SELECT * FROM orders WHERE fp_order_id=?", (str(fp_order_id).lstrip("#"),))

    def add_event(self, oid: int, event: str, details: str = "") -> None:
        self.p.db.execute("INSERT INTO order_events(order_id, ts, event, details) VALUES(?,?,?,?)",
                          (oid, now_ts(), event, str(details)[:1000]))

    def events(self, oid: int) -> list[dict]:
        return self.p.db.query("SELECT * FROM order_events WHERE order_id=? ORDER BY id", (oid,))

    def update(self, oid: int, **fields: Any) -> None:
        if not fields:
            return
        fields["updated_at"] = now_ts()
        sets = ", ".join(f"{k}=?" for k in fields)
        self.p.db.execute(f"UPDATE orders SET {sets} WHERE id=?", list(fields.values()) + [oid])

    def set_status(self, oid: int, status: str, details: str = "", **fields: Any) -> dict:
        """Переход состояния с записью в order_events."""
        cur = self.get(oid)
        old = cur["status"] if cur else None
        self.update(oid, status=status, **fields)
        self.add_event(oid, "status", f"{old} -> {status}" + (f": {details}" if details else ""))
        log_info(f"Заказ #{cur['fp_order_id'] if cur else oid}: {old} -> {status} {details}")
        return self.get(oid)

    def active_for_buyer(self, buyer: str, exclude_id: int = 0) -> int:
        statuses = (ORDER_WAIT_LINK,) + BUSY_ORDER_STATUSES
        return int(self.p.db.scalar(
            f"SELECT COUNT(*) FROM orders WHERE buyer=? AND id<>? AND status IN ({','.join('?' * len(statuses))})",
            (buyer, exclude_id) + statuses, 0))

    def lot_of(self, order: dict) -> Optional[dict]:
        return self.p.db.one("SELECT * FROM lots WHERE id=?", (order["lot_id"],)) if order.get("lot_id") else None

    def primary_service(self, order: dict) -> Optional[dict]:
        if order.get("supplier_id") and order.get("service_id"):
            s = self.p.sup.service(order["supplier_id"], order["service_id"])
            if s:
                return s
        cands = self.p.price.lot_candidates(order["lot_id"], usable_only=False) if order.get("lot_id") else []
        return cands[0] if cands else None

    # ── новый заказ ──
    def match_lot(self, order: Any) -> Optional[dict]:
        """Ищет наш лот по подкатегории и названию заказа; чужие лоты игнорируются."""
        desc = norm_text(getattr(order, "description", ""))
        node = order.subcategory.id if getattr(order, "subcategory", None) else None
        lots = self.p.db.query("SELECT * FROM lots WHERE enabled=1 AND lost=0 AND fp_lot_id IS NOT NULL")
        best, best_len = None, 0
        for lot in lots:
            if node and lot["node_id"] and int(lot["node_id"]) != int(node):
                continue
            title = norm_text(lot["title"])
            if title and title in desc and len(title) > best_len:
                best, best_len = lot, len(title)
        return best

    def lot_texts(self, lot: dict) -> tuple[str, str]:
        """(текст автовыдачи, текст автоответа) из шаблона лота."""
        try:
            t = self.p.ml.template(lot["template_id"]) if lot.get("template_id") else None
            if not t or not lot.get("supplier_id"):
                return "", ""
            svc = self.p.sup.service(lot["supplier_id"], lot["service_id"])
            if not svc:
                return "", ""
            b = self.p.ml.build(t, lot["supplier_id"], svc, int(lot.get("pack_qty") or 0), lot)
            return b["secrets"], b["autoreply"]
        except Exception:
            log_error("lot_texts", exc=True)
            return "", ""

    def handle_new_order(self, event: NewOrderEvent) -> None:
        """BIND_TO_NEW_ORDER: регистрирует заказ (идемпотентно) и запускает автомат."""
        o = event.order
        lot = self.match_lot(o)
        if not lot:
            return
        with self.lock:
            if self.by_fp(o.id):
                return
            amount = int(o.amount or 1)
            qty = self.p.price.lot_unit(lot) * amount
            ts = now_ts()
            changed = self.p.db.rowcount(
                "INSERT OR IGNORE INTO orders(fp_order_id, buyer, lot_id, quantity, price_paid, status, created_at, "
                "updated_at, chat_id, fp_amount, tried) VALUES(?,?,?,?,?,?,?,?,?,?,'[]')",
                (str(o.id), o.buyer_username, lot["id"], qty, str(D(o.price)), ORDER_NEW, ts, ts, str(o.chat_id),
                 amount))
            if not changed:
                return
            order = self.by_fp(o.id)
        self.p.db.execute("UPDATE lots SET last_sale_at=?, discount_active=0 WHERE id=?", (now_ts(), lot["id"]))
        self.add_event(order["id"], "created", f"lot={lot['id']} amount={amount} qty={qty} price={o.price}")
        log_info(f"Новый заказ #{o.id} от {o.buyer_username}: лот {lot['id']}, {qty} шт.")
        if self.p.cfg.get("auto.notify_new_orders"):
            self.p.alerts.send(f"🆕 Заказ #{esc(o.id)} от {esc(o.buyer_username)}: {esc(lot['title'][:60])}, "
                               f"{qty} шт., {money(o.price)} ₽", kb=self.p.ui.order_kb(order["id"]))
        bl = self.p.db.one("SELECT * FROM blacklist WHERE buyer=?", (o.buyer_username,))
        if bl:
            self.update(order["id"], error="blacklist")
            self.p.alerts.send(f"⛔ Заказ #{esc(o.id)} от покупателя из ЧС {esc(o.buyer_username)} "
                               f"({esc(bl['reason'] or '')}).", kb=self.p.ui.order_kb(order["id"]))
            if self.p.cfg.get("blacklist_refund"):
                self.refund_full(self.get(order["id"]), "blacklist", notify_buyer=False, code="blacklist")
            else:
                self.set_status(order["id"], ORDER_FAILED, "покупатель в чёрном списке", problem=1)
            return
        per_hour = int(self.p.cfg.get("auto.max_orders_per_buyer_hour"))
        if per_hour:
            recent = int(self.p.db.scalar("SELECT COUNT(*) FROM orders WHERE buyer=? AND created_at>=?",
                                          (o.buyer_username, now_ts() - 3600), 0))
            if recent > per_hour:
                self.refund_full(self.get(order["id"]), "лимит заказов в час", code="limit")
                return
        cands = self.p.price.lot_candidates(lot["id"], usable_only=False)
        if cands and not any(int(c["min"] or 1) <= qty <= int(c["max"] or 10 ** 9) for c in cands
                             if c["rate"] is not None):
            self.add_event(order["id"], "problem", "количество вне min/max всех кандидатов")
            if self.p.cfg.get("auto.refund_on_fail"):
                self.refund_full(self.get(order["id"]), "количество вне min/max", code="qty")
            else:
                self.update(order["id"], problem=1, error="qty_out_of_range")
                self.p.alerts.send(f"⚠️ Заказ #{esc(o.id)}: количество {qty} вне пределов min/max услуг лота.",
                                   kb=self.p.ui.order_kb(order["id"]))
            return
        self.try_start(self.get(order["id"]))

    def try_start(self, order: dict) -> None:
        """NEW -> WAIT_LINK, если не превышен лимит активных заказов покупателя."""
        limit = int(self.p.cfg.get("max_active_per_buyer"))
        if limit and self.active_for_buyer(order["buyer"], order["id"]) >= limit:
            if not self.p.db.one("SELECT 1 FROM order_events WHERE order_id=? AND event='queued_limit'",
                                 (order["id"],)):
                self.add_event(order["id"], "queued_limit", f"лимит {limit}")
                self.p.msg.send(order, "queued_limit")
            return
        order = self.set_status(order["id"], ORDER_WAIT_LINK, confirm_deadline=now_ts(), link_reminded=0)
        lot = self.lot_of(order)
        self.p.msg.send(order, "accepted")
        secrets_text, _ = self.lot_texts(lot) if lot else ("", "")
        if secrets_text:
            self.p.msg.send_raw(order["chat_id"], order["buyer"], secrets_text)
        self.p.msg.send(order, "ask_link")

    # ── сообщения покупателя ──
    def handle_message(self, event: NewMessageEvent) -> None:
        """BIND_TO_NEW_MESSAGE: ссылка, подтверждение, промокод, докрутка, вопрос о статусе."""
        m = event.message
        if not m.text or m.by_bot or not m.author_id:
            return
        if m.author_id == self.p.c.account.id:
            return
        text = m.text.strip()
        chat_id = str(m.chat_id)
        with self.lock:
            promo = PROMO_RX.search(text.upper())
            if promo:
                self.apply_promo(chat_id, m.author or "", promo.group(0))
                return
            waiting = self.p.db.one("SELECT * FROM orders WHERE chat_id=? AND status IN (?,?) ORDER BY id LIMIT 1",
                                    (chat_id, ORDER_WAIT_LINK, ORDER_WAIT_CONFIRM))
            if waiting:
                if waiting["status"] == ORDER_WAIT_LINK:
                    if URL_RX.search(text) or not self._is_chatter(text):
                        self.process_link(waiting, text)
                    return
                if text in ("+", "＋", "да", "Да", "ok", "ок", "Ок", "OK", "Ok"):
                    # Повторный «+» не создаёт второй отправки: статус меняется только из WAIT_CONFIRM.
                    if self.p.db.rowcount("UPDATE orders SET status=?, updated_at=? WHERE id=? AND status=?",
                                          (ORDER_SENDING, now_ts(), waiting["id"], ORDER_WAIT_CONFIRM)):
                        self.add_event(waiting["id"], "status", f"{ORDER_WAIT_CONFIRM} -> {ORDER_SENDING}: "
                                                               f"подтверждено покупателем")
                        self.add_event(waiting["id"], "confirmed", "")
                    return
                if text in ("-", "−", "нет", "Нет"):
                    self.set_status(waiting["id"], ORDER_WAIT_LINK, "покупатель меняет ссылку", link=None,
                                    link_attempts=0, confirm_deadline=now_ts(), link_reminded=0)
                    self.p.msg.send(self.get(waiting["id"]), "ask_link")
                    return
                if URL_RX.search(text):
                    self.process_link(waiting, text)
                    return
        if self.p.cfg.get("auto.refill_requests"):
            try:
                rrx = re.compile(self.p.cfg.get("auto.refill_regex"), re.I)
            except re.error:
                rrx = re.compile(DEFAULTS["auto"]["refill_regex"], re.I)
            if rrx.search(text):
                self.handle_refill_request(chat_id)
                return
        try:
            rx = re.compile(self.p.cfg.get("status_regex"), re.I)
        except re.error:
            rx = re.compile(DEFAULTS["status_regex"], re.I)
        if rx.search(text):
            order = self.p.db.one("SELECT * FROM orders WHERE chat_id=? AND status IN (?,?,?,?) ORDER BY id DESC "
                                  "LIMIT 1", (chat_id, ORDER_NEW, ORDER_SENDING, ORDER_IN_PROGRESS, ORDER_UNCERTAIN))
            if order and now_ts() - int(order["last_status_reply"] or 0) >= int(self.p.cfg.get("status_reply_cooldown")):
                self.update(order["id"], last_status_reply=now_ts())
                self.p.msg.send(order, "status")

    @staticmethod
    def _is_chatter(text: str) -> bool:
        """Короткие фразы вроде «привет», «ок, сейчас» не считаются попыткой отправить ссылку."""
        t = text.strip().lower()
        if "." in t and " " not in t:
            return False
        return len(t) < 40 and bool(re.match(r"^[\w\s,!?.)(:-]+$", t)) and not re.search(r"[/@]", t)

    def process_link(self, order: dict, text: str) -> None:
        m = URL_RX.search(text)
        link = m.group(0).rstrip(").,;!?»\"'") if m else text.strip()
        if len(URL_RX.findall(text)) > 1:
            err = "пришлите одну ссылку"
        else:
            svc = self.primary_service(order)
            platform = detect_platform(svc.get("name"), svc.get("category")) if svc else None
            err = validate_link(link, platform)
        if err:
            attempts = int(order["link_attempts"] or 0) + 1
            self.update(order["id"], link_attempts=attempts)
            self.add_event(order["id"], "bad_link", f"{err}: {mask_link(link)}")
            if attempts >= int(self.p.cfg.get("link_attempts")):
                if self.p.cfg.get("auto.link_attempts_refund"):
                    self.refund_full(self.get(order["id"]), "попытки ввода ссылки", code="link_attempts")
                    return
                if not order["problem"]:
                    self.update(order["id"], problem=1, error="link_attempts")
                    self.p.alerts.send(f"🔗 Заказ #{esc(order['fp_order_id'])}: покупатель {esc(order['buyer'])} "
                                       f"{attempts} раз прислал неверную ссылку.", kb=self.p.ui.order_kb(order["id"]))
            self.p.msg.send(order, "bad_link", {"status": err})
            return
        limit = int(self.p.cfg.get("max_active_per_link"))
        busy = int(self.p.db.scalar(
            f"SELECT COUNT(*) FROM orders WHERE link=? AND id<>? AND status IN ({','.join('?' * len(BUSY_ORDER_STATUSES))})",
            (link, order["id"]) + BUSY_ORDER_STATUSES, 0))
        if limit and busy >= limit:
            self.add_event(order["id"], "link_busy", mask_link(link))
            self.p.msg.send(order, "link_busy")
            return
        order = self.set_status(order["id"], ORDER_WAIT_CONFIRM, mask_link(link), link=link,
                                confirm_deadline=now_ts() + int(self.p.cfg.get("confirm_timeout")) * 60, reminded=0)
        self.p.msg.send(order, "confirm")

    def apply_promo(self, chat_id: str, buyer: str, code: str) -> None:
        promo = self.p.db.one("SELECT * FROM promo WHERE code=? AND used=0", (code,))
        order = self.p.db.one("SELECT * FROM orders WHERE chat_id=? AND status IN (?,?,?) ORDER BY id DESC LIMIT 1",
                              (chat_id, ORDER_NEW, ORDER_WAIT_LINK, ORDER_WAIT_CONFIRM))
        if not promo or not order or (promo["buyer"] and promo["buyer"] != buyer) or int(order["bonus_pct"] or 0):
            return
        # Атомарно: промокод используется ровно один раз даже при двойной отправке сообщения.
        if not self.p.db.rowcount("UPDATE promo SET used=1 WHERE code=? AND used=0", (code,)):
            return
        self.update(order["id"], bonus_pct=int(promo["percent"]))
        self.add_event(order["id"], "promo", f"{code} +{promo['percent']}%")
        self.p.msg.send(self.get(order["id"]), "promo_applied", {"progress": f"+{promo['percent']}%"})

    def handle_refill_request(self, chat_id: str) -> None:
        """Автодокрутка: покупатель пишет о списании — плагин сам отправляет refill поставщику."""
        window = now_ts() - int(self.p.cfg.get("auto.refill_window_days")) * 86400
        order = self.p.db.one("SELECT * FROM orders WHERE chat_id=? AND status IN (?,?,?) AND completed_at>=? "
                              "AND supplier_order_id IS NOT NULL ORDER BY id DESC LIMIT 1",
                              (chat_id, ORDER_COMPLETED, ORDER_CLOSED, ORDER_PARTIAL, window))
        if not order:
            return
        cooldown = int(self.p.cfg.get("auto.refill_cooldown_hours")) * 3600
        if order["last_refill_at"] and now_ts() - int(order["last_refill_at"]) < cooldown:
            left = fmt_duration(cooldown - (now_ts() - int(order["last_refill_at"])))
            self.p.msg.send(order, "refill_denied", {"status": f"повторный запрос возможен через {left}"})
            return
        svc = self.p.sup.service(order["supplier_id"], order["service_id"]) or {}
        if not to_bool(svc.get("refill")):
            self.p.msg.send(order, "refill_denied", {"status": "у этой услуги нет гарантии докрутки"})
            return
        s = self.p.sup.get(order["supplier_id"])
        try:
            res = s.refill(order["supplier_order_id"]) if s else None
        except SupplierError as e:
            self.add_event(order["id"], "refill_error", e.message)
            self.p.alerts.send(f"♻️ Автодокрутка #{esc(order['fp_order_id'])} не удалась: {esc(e.message)}",
                               kb=self.p.ui.order_kb(order["id"]))
            return
        self.update(order["id"], last_refill_at=now_ts())
        self.add_event(order["id"], "refill", f"{order['supplier_id']}:{order['service_id']} "
                                              f"{json.dumps(res, ensure_ascii=False)[:150]}")
        self.p.msg.send(order, "refill_ok")

    # ── воркер ──
    def restore(self) -> None:
        """После перезапуска: активные заказы восстанавливаются из базы.

        Заказ, у которого отправка поставщику началась, но результат не записан (сбой посреди create_order),
        не отправляется повторно автоматически — он уходит в UNCERTAIN на решение админа.
        """
        rows = self.p.db.query(f"SELECT * FROM orders WHERE status IN "
                               f"({','.join('?' * len(ACTIVE_ORDER_STATUSES))})", ACTIVE_ORDER_STATUSES)
        for r in rows:
            if r["status"] == ORDER_IN_PROGRESS:
                self.update(r["id"], next_poll_at=now_ts())
            elif r["status"] == ORDER_SENDING and r["send_started_at"]:
                self.mark_uncertain(r, "перезапуск во время отправки поставщику")
            self.add_event(r["id"], "restored", r["status"])
        if rows:
            log_info(f"Восстановлено активных заказов: {len(rows)}")

    def tick(self) -> None:
        """Один проход воркера заказов."""
        now = now_ts()
        for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND problem=0 ORDER BY id", (ORDER_NEW,)):
            self.try_start(o)
        link_timeout = int(self.p.cfg.get("auto.link_timeout_hours")) * 3600
        if link_timeout:
            for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND confirm_deadline IS NOT NULL",
                                     (ORDER_WAIT_LINK,)):
                waited = now - int(o["confirm_deadline"] or o["created_at"])
                if waited >= link_timeout:
                    self.refund_full(o, "нет ссылки", code="link_timeout")
                elif waited >= link_timeout // 2 and not o["link_reminded"]:
                    self.update(o["id"], link_reminded=1)
                    self.add_event(o["id"], "link_reminder", "")
                    self.p.msg.send(o, "link_reminder")
        for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND COALESCE(next_poll_at,0)<=? ORDER BY id",
                                 (ORDER_SENDING, now)):
            if self.p.stop.is_set():
                return
            with self.lock:
                fresh = self.get(o["id"])
                if fresh and fresh["status"] == ORDER_SENDING:
                    self.send_to_supplier(fresh)
        for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND confirm_deadline<=?",
                                 (ORDER_WAIT_CONFIRM, now)):
            timeout = int(self.p.cfg.get("confirm_timeout")) * 60
            if int(o["reminded"] or 0) == 0:
                self.update(o["id"], reminded=1, confirm_deadline=now + timeout)
                self.add_event(o["id"], "reminder", "")
                self.p.msg.send(o, "confirm_reminder")
            elif int(o["reminded"] or 0) == 1:
                if self.p.cfg.get("auto.confirm_auto_start") and o["link"]:
                    if self.p.db.rowcount("UPDATE orders SET status=?, reminded=2, updated_at=? WHERE id=? AND "
                                          "status=?", (ORDER_SENDING, now, o["id"], ORDER_WAIT_CONFIRM)):
                        self.add_event(o["id"], "status", f"{ORDER_WAIT_CONFIRM} -> {ORDER_SENDING}: автозапуск")
                        self.p.msg.send(self.get(o["id"]), "auto_started")
                    continue
                self.update(o["id"], reminded=2, problem=1, error="confirm_timeout")
                self.add_event(o["id"], "escalated", "нет подтверждения")
                self.p.alerts.send(f"⏰ Заказ #{esc(o['fp_order_id'])}: покупатель не подтверждает "
                                   f"{2 * timeout // 60} мин.", kb=self.p.ui.order_kb(o["id"]))
        for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND COALESCE(next_poll_at,0)<=? ORDER BY "
                                 "next_poll_at LIMIT 50", (ORDER_IN_PROGRESS, now)):
            if self.p.stop.is_set():
                return
            with self.lock:
                fresh = self.get(o["id"])
                if fresh and fresh["status"] == ORDER_IN_PROGRESS:
                    self.poll(fresh)
        for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND COALESCE(next_poll_at,0)<=?",
                                 (ORDER_REFUND_PENDING, now)):
            self.refund_full(o, o["refund_reason"] or "повтор возврата", code=o["error"] if o["error"] in
                             REFUND_REASONS else None, retry=True)
        unc_hours = int(self.p.cfg.get("auto.uncertain_refund_hours"))
        if unc_hours:
            for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND updated_at<=?",
                                     (ORDER_UNCERTAIN, now - unc_hours * 3600)):
                self.refund_full(o, "неясная отправка", code="uncertain")
        remind = int(self.p.cfg.get("auto.confirm_reminder_hours")) * 3600
        if remind:
            for o in self.p.db.query("SELECT * FROM orders WHERE status=? AND confirm_reminded=0 AND completed_at<=?",
                                     (ORDER_COMPLETED, now - remind)):
                self.update(o["id"], confirm_reminded=1)
                self.p.msg.send(o, "confirm_please")
        stuck = int(self.p.cfg.get("alerts.stuck_hours")) * 3600
        for o in self.p.db.query("SELECT * FROM orders WHERE status IN (?,?) AND updated_at<? AND problem=0",
                                 (ORDER_SENDING, ORDER_IN_PROGRESS, now - stuck)):
            self.p.alerts.send(f"🐢 Заказ #{esc(o['fp_order_id'])} завис: {o['status']} больше "
                               f"{stuck // 3600} ч.", key=f"stuck:{o['id']}", kb=self.p.ui.order_kb(o["id"]))

    @staticmethod
    def pick_reason(reasons: dict, errors: list[str]) -> str:
        """Самая понятная причина отказа из исключений кандидатов и ошибок поставщиков."""
        merged = dict(reasons)
        for e in errors:
            merged[e] = merged.get(e, 0) + 1
        for code in ("no_balance", "auth", "link", "service", "api_down", "no_api", "fx", "qty", "no_supplier"):
            if merged.get(code):
                return code
        if any(e in TRANSIENT_CODES for e in errors):
            return "api_down"
        return "all_failed" if errors else "no_supplier"

    def mark_uncertain(self, order: dict, reason: str) -> None:
        """Отправка могла пройти, а могла нет: повтор = риск двойной выдачи, поэтому решает админ."""
        self.set_status(order["id"], ORDER_UNCERTAIN, reason, problem=1, error="uncertain", send_started_at=None)
        kb = K()
        kb.row(B("✅ Заказ создан — ввести ID", callback_data=self.p.ui.cb("ounc", order["id"])),
               B("🔁 Не создан — отправить", callback_data=self.p.ui.cb("oact", order["id"], "resend")))
        kb.row(B("💸 Вернуть деньги", callback_data=self.p.ui.cb("oref", order["id"])),
               B("🧾 Карточка", callback_data=self.p.ui.cb("od", order["id"])))
        hours = int(self.p.cfg.get("auto.uncertain_refund_hours"))
        self.p.alerts.send(f"❓ Заказ #{esc(order['fp_order_id'])}: {esc(reason)}.\nПроверьте в кабинете поставщика, "
                           f"создан ли заказ на ссылку {esc(order.get('link') or '')}. Автоповтор отключён, чтобы не "
                           f"выдать дважды." + (f"\nБез решения через {hours} ч — автовозврат." if hours else ""),
                           kb=kb)

    def send_to_supplier(self, order: dict) -> None:
        """SENDING: выбор кандидата и create_order с автоматическим fallback и защитой от двойной отправки."""
        lot = self.lot_of(order)
        if not lot:
            self.refund_full(order, "лот удалён", code="no_supplier")
            return
        if not order.get("link"):
            self.set_status(order["id"], ORDER_WAIT_LINK, "нет ссылки", confirm_deadline=now_ts())
            return
        if order.get("supplier_order_id"):
            # Защита: у заказа уже есть номер у поставщика — повторно не отправляем.
            self.set_status(order["id"], ORDER_IN_PROGRESS, "уже отправлен ранее", next_poll_at=now_ts())
            return
        qty = int(order["quantity"]) + int(order["quantity"]) * int(order["bonus_pct"] or 0) // 100
        tried = set(json.loads(order["tried"] or "[]"))
        reasons: dict = {}
        try:
            cands = self.p.cat.select_candidates(lot, qty, tried, reasons)
        except SupplierError as e:
            cands, reasons = [], {e.code: 1}
        errors: list[str] = []
        for cand in cands:
            key = f"{cand['supplier_id']}:{cand['service_id']}"
            s = self.p.sup.get(cand["supplier_id"])
            self.update(order["id"], send_started_at=now_ts())
            self.add_event(order["id"], "send_attempt", f"{key} qty={qty}")
            try:
                soid = s.create_order(cand["service_id"], order["link"], qty)
            except SupplierError as e:
                if e.code == "uncertain":
                    self.update(order["id"], supplier_id=cand["supplier_id"], service_id=str(cand["service_id"]),
                                cost=str(cand["cost_rub"].quantize(Decimal("0.01"))))
                    self.add_event(order["id"], "supplier_uncertain", f"{key} {e.message}")
                    self.mark_uncertain(self.get(order["id"]), f"{s.name}: {e.message}")
                    return
                self.update(order["id"], send_started_at=None)
                tried.add(key)
                errors.append(e.code)
                self.add_event(order["id"], "supplier_fail", f"{key} {e.code}: {e.message}")
                self.p.sup.mark_error(cand["supplier_id"], e.message)
                if e.code == "no_balance":
                    self.p.sup.invalidate_balance(cand["supplier_id"])
                    self.p.auto.on_no_balance(cand["supplier_id"])
                elif e.code == "auth":
                    self.p.alerts.send(f"🔑 {esc(s.name)}: ошибка авторизации API — {esc(e.message)}",
                                       key=f"auth:{cand['supplier_id']}")
                self.add_event(order["id"], "fallback", f"следующий кандидат после {key}")
                continue
            tried.add(key)
            self.p.sup.mark_ok(cand["supplier_id"])
            self.p.sup.invalidate_balance(cand["supplier_id"])
            eta = self.p.cat.eta_seconds(cand["supplier_id"], cand["service_id"], cand["category"] or "",
                                         cand["name"] or "")
            order = self.set_status(order["id"], ORDER_IN_PROGRESS, f"{s.name} #{soid}",
                                    supplier_id=cand["supplier_id"], service_id=str(cand["service_id"]),
                                    supplier_order_id=soid, cost=str(cand["cost_rub"].quantize(Decimal("0.01"))),
                                    sent_at=now_ts(), next_poll_at=now_ts() + int(self.p.cfg.get("poll_interval")),
                                    eta_text=fmt_duration(eta), tried=json.dumps(sorted(tried)), poll_count=0,
                                    remain=None, delayed_notified=0, error=None, send_started_at=None,
                                    first_error_at=None)
            self.add_event(order["id"], "sent", f"{key} supplier_order={soid} qty={qty}")
            self.p.msg.send(order, "in_progress")
            _, autoreply = self.lot_texts(lot)
            if autoreply:
                self.p.msg.send_raw(order["chat_id"], order["buyer"], self.p.msg.render(
                    autoreply, self.p.msg.order_values(order)))
            return
        code = self.pick_reason(reasons, errors)
        # Сеть/пауза поставщика — временно: повторяем в окне transient_retry_min. Нет баланса, ключа или услуги —
        # ждать бессмысленно: сразу автовозврат.
        transient = code == "api_down" or (bool(errors) and all(e in TRANSIENT_CODES for e in errors))
        first = int(order["first_error_at"] or now_ts())
        window = int(self.p.cfg.get("auto.transient_retry_min")) * 60
        if code == "link" and int(order["link_attempts"] or 0) < int(self.p.cfg.get("link_attempts")):
            # Поставщик не принял ссылку — просим другую вместо возврата.
            self.set_status(order["id"], ORDER_WAIT_LINK, "поставщик отклонил ссылку", link=None,
                            link_attempts=int(order["link_attempts"] or 0) + 1, tried="[]",
                            confirm_deadline=now_ts(), link_reminded=0)
            self.p.msg.send(self.get(order["id"]), "bad_link",
                            {"status": "сервис не принял ссылку — проверьте, что профиль открыт"})
            return
        if transient and now_ts() - first < window:
            # Временная проблема (сеть, пауза поставщика, ожидание пополнения) — повторяем позже.
            self.update(order["id"], first_error_at=first, next_poll_at=now_ts() + 120, tried="[]")
            self.add_event(order["id"], "retry_later", f"{code}: повтор через 2 мин")
            return
        self.update(order["id"], tried=json.dumps(sorted(tried)), first_error_at=None)
        if self.p.cfg.get("auto.refund_on_fail"):
            self.refund_full(self.get(order["id"]), REFUND_REASONS.get(code, ("", code))[1], code=code)
        else:
            self.set_status(order["id"], ORDER_FAILED, REFUND_REASONS.get(code, ("", code))[1], error=code, problem=1)
            self.p.alerts.send(f"❌ Заказ #{esc(order['fp_order_id'])} не отправлен: "
                               f"{esc(REFUND_REASONS.get(code, ('', code))[1])}", kb=self.p.ui.order_kb(order["id"]))

    def poll(self, order: dict) -> None:
        """IN_PROGRESS: опрос статуса у поставщика."""
        s = self.p.sup.get(order["supplier_id"]) if order.get("supplier_id") else None
        base = int(self.p.cfg.get("poll_interval"))
        elapsed = now_ts() - int(order["sent_at"] or now_ts())
        interval = int(min(900, base * (1 + elapsed / 7200)))
        if not s:
            self.update(order["id"], problem=1, error="supplier_missing", next_poll_at=now_ts() + 3600)
            return
        try:
            st = s.get_status(order["supplier_order_id"])
        except SupplierError as e:
            self.update(order["id"], next_poll_at=now_ts() + interval, poll_count=int(order["poll_count"] or 0) + 1)
            self.add_event(order["id"], "poll_error", f"{e.code}: {e.message}")
            return
        remain = st.get("remain")
        self.update(order["id"], remain=remain, start_count=st.get("start_count"), supplier_status=st["raw_status"],
                    poll_count=int(order["poll_count"] or 0) + 1, next_poll_at=now_ts() + interval)
        order = self.get(order["id"])
        status = st["status"]
        qty = int(order["quantity"])
        if status == "COMPLETED":
            self.complete(order)
        elif status == "PARTIAL" or (status == "CANCELED" and remain is not None and 0 < int(remain) < qty):
            self.partial(order, int(remain or 0))
        elif status in ("CANCELED", "FAILED"):
            self.failover(order, f"статус {st['raw_status']}")
        else:
            if elapsed > int(self.p.cfg.get("max_wait_hours")) * 3600:
                try:
                    s.cancel(order["supplier_order_id"])
                    self.add_event(order["id"], "cancel_request", "таймаут")
                except SupplierError as e:
                    self.add_event(order["id"], "cancel_error", e.message)
                self.failover(order, "таймаут max_wait_hours")
                return
            svc = self.primary_service(order) or {}
            eta = self.p.cat.eta_seconds(order["supplier_id"], order["service_id"], svc.get("category", ""),
                                         svc.get("name", ""))
            if not order["delayed_notified"] and elapsed > eta * 1.5:
                self.update(order["id"], delayed_notified=1)
                self.add_event(order["id"], "delayed", f"elapsed={elapsed}")
                self.p.msg.send(self.get(order["id"]), "delayed")

    def complete(self, order: dict) -> None:
        order = self.set_status(order["id"], ORDER_COMPLETED, completed_at=now_ts(), remain=0, problem=0)
        self.p.msg.send(order, "completed")
        self.p.cat.recompute_stats(order["supplier_id"], order["service_id"])
        self.loyalty(order)

    def partial(self, order: dict, remain: int) -> None:
        """Частичное выполнение: по политике — дозаказ остатка, затем возврат или решение админа."""
        qty = max(1, int(order["quantity"]))
        due = (D(order["price_paid"]) * D(remain) / D(qty)).quantize(Decimal("0.01"), rounding=ROUND_FLOOR)
        self.p.cat.recompute_stats(order["supplier_id"], order["service_id"])
        policy = self.p.cfg.get("auto.partial_policy")
        reorders = int(self.p.db.scalar("SELECT COUNT(*) FROM order_events WHERE order_id=? AND "
                                        "event='reorder_remain'", (order["id"],), 0))
        if policy.startswith("reorder") and reorders < 2:
            msg = self.reorder_remain(order, remain, exclude_current=True)
            if msg is None:
                return
            self.add_event(order["id"], "reorder_failed", msg)
        order = self.set_status(order["id"], ORDER_PARTIAL, f"остаток {remain}, к возврату {due}",
                                remain=remain, refund_due=str(due), completed_at=now_ts(), problem=1)
        if policy in ("reorder_then_refund", "refund"):
            # TODO: подтвердить метод Cardinal — частичного возврата в FunPayAPI нет, поэтому возвращается вся сумма.
            self.refund_full(order, f"частичное выполнение (остаток {remain})", code="partial")
            return
        self.p.msg.send(order, "partial")
        kb = K()
        kb.row(B("💸 Полный возврат", callback_data=self.p.ui.cb("oref", order["id"])),
               B("🔁 Дозаказать остаток", callback_data=self.p.ui.cb("oact", order["id"], "reorder")))
        kb.row(B("✅ Закрыть", callback_data=self.p.ui.cb("oact", order["id"], "close")),
               B("🧾 Карточка", callback_data=self.p.ui.cb("od", order["id"])))
        self.p.alerts.send(f"🌓 Заказ #{esc(order['fp_order_id'])} выполнен частично: остаток {remain} из {qty}.\n"
                           f"Рассчитанный возврат: <b>{money(due)} ₽</b> (оплачено {money(order['price_paid'])} ₽).",
                           kb=kb)

    def reorder_remain(self, order: dict, remain: int, exclude_current: bool = False) -> Optional[str]:
        """Дозаказ остатка у кандидата. None — успех, иначе текст причины."""
        if remain <= 0 or not order.get("link"):
            return "нет остатка или ссылки"
        lot = self.lot_of(order)
        if not lot:
            return "лот удалён"
        exclude = {f"{order['supplier_id']}:{order['service_id']}"} if exclude_current else set()
        cands = self.p.cat.select_candidates(lot, remain, exclude)
        if not cands and exclude_current:
            cands = self.p.cat.select_candidates(lot, remain, set())
        for cand in cands:
            sup = self.p.sup.get(cand["supplier_id"])
            key = f"{cand['supplier_id']}:{cand['service_id']}"
            self.update(order["id"], send_started_at=now_ts())
            try:
                soid = sup.create_order(cand["service_id"], order["link"], remain)
            except SupplierError as e:
                self.update(order["id"], send_started_at=None)
                if e.code == "uncertain":
                    self.mark_uncertain(self.get(order["id"]), f"дозаказ остатка: {e.message}")
                    return None
                self.add_event(order["id"], "supplier_fail", f"{key} {e.code}: {e.message}")
                continue
            self.set_status(order["id"], ORDER_IN_PROGRESS, f"дозаказ остатка {remain}: {sup.name} #{soid}",
                            supplier_id=cand["supplier_id"], service_id=str(cand["service_id"]),
                            supplier_order_id=soid, sent_at=now_ts(), next_poll_at=now_ts() + 60,
                            problem=0, refund_due=None, remain=None, send_started_at=None,
                            cost=str(D(order["cost"]) + cand["cost_rub"].quantize(Decimal("0.01"))))
            self.add_event(order["id"], "reorder_remain", f"{key} qty={remain}")
            return None
        return "нет кандидатов для дозаказа"

    def failover(self, order: dict, reason: str) -> None:
        """Отказ/ошибка поставщика → следующий кандидат (покупатель не уведомляется)."""
        key = f"{order['supplier_id']}:{order['service_id']}"
        self.add_event(order["id"], "supplier_fail", f"{key} {reason}")
        self.add_event(order["id"], "fallback", f"после {key}: {reason}")
        self.p.cat.recompute_stats(order["supplier_id"], order["service_id"])
        tried = set(json.loads(order["tried"] or "[]"))
        tried.add(key)
        self.set_status(order["id"], ORDER_SENDING, f"fallback: {reason}", tried=json.dumps(sorted(tried)),
                        supplier_order_id=None, poll_count=0, next_poll_at=now_ts())

    def refund_full(self, order: dict, reason: str, notify_buyer: bool = True, code: Optional[str] = None,
                    retry: bool = False) -> bool:
        """Полный возврат через FunPay. Идемпотентен: один заказ возвращается не более одного раза.

        code — причина из REFUND_REASONS (покупатель получит понятный текст автовозврата).
        Если FunPay не принял возврат — заказ уходит в REFUND_PENDING и возврат повторяется автоматически.
        """
        with self.lock:
            fresh = self.get(order["id"])
            if not fresh or fresh["status"] == ORDER_REFUNDED:
                return True
            if fresh["status"] == ORDER_IN_PROGRESS and fresh["supplier_order_id"]:
                s = self.p.sup.get(fresh["supplier_id"])
                try:
                    if s:
                        s.cancel(fresh["supplier_order_id"])
                        self.add_event(fresh["id"], "cancel_request", "перед возвратом")
                except SupplierError as e:
                    self.add_event(fresh["id"], "cancel_error", e.message)
            if self.p.dry:
                log_info(f"[DRY-RUN] Возврат заказа #{fresh['fp_order_id']} ({reason})")
            else:
                try:
                    with self.p.fp_lock:
                        self.p.c.account.refund(fresh["fp_order_id"])
                except Exception as e:
                    attempts = int(fresh["refund_attempts"] or 0) + 1
                    log_error(f"Возврат заказа #{fresh['fp_order_id']} не удался ({attempts}): {e}", exc=True)
                    if attempts < int(self.p.cfg.get("auto.refund_retry_max")):
                        self.set_status(fresh["id"], ORDER_REFUND_PENDING, f"возврат не удался: {e}"[:200],
                                        refund_attempts=attempts, refund_reason=reason, error=code or "refund",
                                        next_poll_at=now_ts() + int(self.p.cfg.get("auto.refund_retry_min")) * 60)
                        if attempts == 1:
                            self.p.alerts.send(f"⌛ Возврат #{esc(fresh['fp_order_id'])} не прошёл, повторю "
                                               f"автоматически: {esc(str(e)[:150])}", kb=self.p.ui.order_kb(fresh["id"]))
                    else:
                        self.set_status(fresh["id"], ORDER_FAILED, f"возврат не удался: {e}"[:200],
                                        refund_attempts=attempts, error=f"refund: {e}"[:300], problem=1)
                        self.p.alerts.send(f"❗ Не удалось вернуть деньги по заказу #{esc(fresh['fp_order_id'])} "
                                           f"после {attempts} попыток: {esc(str(e)[:200])}",
                                           kb=self.p.ui.order_kb(fresh["id"]))
                    return False
            order = self.set_status(fresh["id"], ORDER_REFUNDED, reason, refunded_amount=str(fresh["price_paid"]),
                                    error=(code or reason)[:300], refund_reason=reason, send_started_at=None)
        if notify_buyer:
            if code and code in REFUND_REASONS and code != "manual":
                self.p.msg.send(order, "auto_refund", {"status": REFUND_REASONS[code][0]})
            else:
                self.p.msg.send(order, "canceled")
        admin_reason = REFUND_REASONS[code][1] if code in REFUND_REASONS else reason
        self.p.alerts.send(f"💸 Заказ #{esc(order['fp_order_id'])}: автовозврат {money(order['price_paid'])} ₽ — "
                           f"{esc(admin_reason)}.", key=f"refund:{order['id']}")
        return True

    def loyalty(self, order: dict) -> None:
        """Промокод после 1-го, 3-го и каждого 5-го+ выполненного заказа."""
        if not self.p.cfg.get("loyalty.enabled"):
            return
        n = int(self.p.db.scalar("SELECT COUNT(*) FROM orders WHERE buyer=? AND status IN (?,?)",
                                 (order["buyer"], ORDER_COMPLETED, ORDER_CLOSED), 0))
        if n == 1:
            pct = int(self.p.cfg.get("loyalty.level1"))
        elif n == 3:
            pct = int(self.p.cfg.get("loyalty.level3"))
        elif n >= 5 and n % 5 == 0:
            pct = int(self.p.cfg.get("loyalty.level5"))
        else:
            return
        if pct <= 0:
            return
        code = "ASM-" + "".join(random.choice("ABCDEFGHJKLMNPQRSTUVWXYZ23456789") for _ in range(6))
        self.p.db.execute("INSERT INTO promo(code, buyer, percent, used, ts) VALUES(?,?,?,0,?)",
                          (code, order["buyer"], pct, now_ts()))
        self.add_event(order["id"], "promo_issued", f"{code} {pct}%")
        self.p.msg.send(order, "promo", {"status": code, "progress": f"{pct}%"})

    def handle_status_changed(self, event: OrderStatusChangedEvent) -> None:
        """BIND_TO_ORDER_STATUS_CHANGED: закрытие покупателем / возврат вручную на FunPay."""
        o = event.order
        row = self.by_fp(o.id)
        if not row:
            return
        if o.status == OrderStatuses.CLOSED:
            self.add_event(row["id"], "fp_closed", "покупатель подтвердил заказ")
            if row["status"] == ORDER_COMPLETED:
                self.set_status(row["id"], ORDER_CLOSED, "подтверждён на FunPay")
        elif o.status == OrderStatuses.REFUNDED and row["status"] != ORDER_REFUNDED:
            if row["status"] == ORDER_IN_PROGRESS and row["supplier_order_id"]:
                s = self.p.sup.get(row["supplier_id"])
                try:
                    if s:
                        s.cancel(row["supplier_order_id"])
                        self.add_event(row["id"], "cancel_request", "возврат на FunPay")
                except SupplierError as e:
                    self.add_event(row["id"], "cancel_error", e.message)
            self.set_status(row["id"], ORDER_REFUNDED, "возврат на FunPay", refunded_amount=str(row["price_paid"]))

    # ── ручные действия ──
    def manual(self, oid: int, action: str, arg: str = "") -> str:
        """Ручные действия: retry, resend, refill, cancel, refund, close, reorder, relink, unproblem, set_sent."""
        o = self.get(oid)
        if not o:
            return "Заказ не найден."
        s = self.p.sup.get(o["supplier_id"]) if o.get("supplier_id") else None
        self.add_event(oid, "manual", f"{action} {arg}".strip())
        try:
            if action in ("retry", "resend"):
                if not o["link"]:
                    return "У заказа нет ссылки."
                if o["status"] == ORDER_IN_PROGRESS and o["supplier_order_id"]:
                    return "Заказ уже выполняется у поставщика — повтор создаст дубль. Сначала отмените его."
                self.set_status(oid, ORDER_SENDING, "повтор вручную", tried="[]", problem=0, error=None,
                                poll_count=0, next_poll_at=0, supplier_order_id=None, send_started_at=None,
                                first_error_at=None)
                return "Заказ поставлен в очередь на отправку."
            if action == "set_sent":
                soid = arg.strip()
                if not soid:
                    return "Не указан номер заказа поставщика."
                self.set_status(oid, ORDER_IN_PROGRESS, f"номер у поставщика указан вручную: {soid}",
                                supplier_order_id=soid, sent_at=o["sent_at"] or now_ts(), next_poll_at=now_ts(),
                                problem=0, error=None, send_started_at=None)
                return f"Заказ привязан к #{esc(soid)} у поставщика, отслеживание продолжено."
            if action == "refill":
                if not s or not o["supplier_order_id"]:
                    return "Нет заказа у поставщика."
                res = s.refill(o["supplier_order_id"])
                self.update(oid, last_refill_at=now_ts())
                self.add_event(oid, "refill", f"{o['supplier_id']}:{o['service_id']} {json.dumps(res)[:200]}")
                return f"Refill отправлен: {esc(json.dumps(res, ensure_ascii=False)[:200])}"
            if action == "cancel":
                if not s or not o["supplier_order_id"]:
                    return "Нет заказа у поставщика."
                res = s.cancel(o["supplier_order_id"])
                self.add_event(oid, "cancel_request", json.dumps(res, ensure_ascii=False)[:200])
                return f"Запрос отмены отправлен: {esc(json.dumps(res, ensure_ascii=False)[:200])}"
            if action == "refund":
                if o["status"] == ORDER_REFUNDED:
                    return "Деньги по заказу уже возвращены."
                return "Возврат выполнен." if self.refund_full(o, "вручную", code="manual") else \
                    "Возврат не прошёл — будет повторён автоматически."
            if action == "close":
                self.set_status(oid, ORDER_CLOSED, "закрыт вручную", problem=0)
                return "Заказ закрыт."
            if action == "unproblem":
                self.update(oid, problem=0, error=None)
                return "Отметка «проблемный» снята."
            if action == "relink":
                self.set_status(oid, ORDER_WAIT_LINK, "запрос новой ссылки", link=None, link_attempts=0, problem=0,
                                confirm_deadline=now_ts(), link_reminded=0)
                self.p.msg.send(self.get(oid), "ask_link")
                return "Покупателю отправлен запрос ссылки."
            if action == "reorder":
                remain = int(o["remain"] or 0)
                res = self.reorder_remain(o, remain)
                if res is None:
                    fresh = self.get(oid)
                    if fresh["status"] == ORDER_UNCERTAIN:
                        return "Результат дозаказа неясен — проверьте у поставщика."
                    return f"Остаток {remain} дозаказан (#{esc(fresh['supplier_order_id'])})."
                return f"Дозаказ не выполнен: {esc(res)}."
        except SupplierError as e:
            return f"Ошибка поставщика: {esc(e.message)}"
        return "Неизвестное действие."


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# J. RAISE: автоподнятие лотов
# ═══════════════════════════════════════════════════════════════════════════════════════════════

class Raiser:
    """Автоподнятие категорий; время следующего поднятия берётся из ответа FunPay."""

    def __init__(self, p: "AutoSMM"):
        self.p = p

    def categories(self) -> list[tuple[int, str]]:
        """Категории (игры) FunPay, в которых есть наши лоты."""
        nodes = [r["node_id"] for r in self.p.db.query(
            "SELECT DISTINCT node_id FROM lots WHERE node_id IS NOT NULL AND fp_lot_id IS NOT NULL AND lost=0")]
        result: dict[int, str] = {}
        for node in nodes:
            try:
                sub = self.p.c.account.get_subcategory(SubCategoryTypes.COMMON, int(node))
            except Exception:
                sub = None
            if sub and sub.category:
                result[sub.category.id] = sub.category.name
        return sorted(result.items(), key=lambda x: x[1])

    def selected(self) -> list[tuple[int, str]]:
        chosen = [int(x) for x in (self.p.cfg.get("raise.categories") or [])]
        cats = self.categories()
        if chosen:
            cats = [c for c in cats if c[0] in chosen]
        sales: dict[int, int] = {}
        border = now_ts() - 7 * 86400
        for r in self.p.db.query("SELECT l.node_id, COUNT(*) AS cnt FROM orders o JOIN lots l ON l.id=o.lot_id "
                                 "WHERE o.created_at>=? GROUP BY l.node_id", (border,)):
            try:
                sub = self.p.c.account.get_subcategory(SubCategoryTypes.COMMON, int(r["node_id"]))
                if sub:
                    sales[sub.category.id] = sales.get(sub.category.id, 0) + int(r["cnt"])
            except Exception:
                continue
        return sorted(cats, key=lambda c: -sales.get(c[0], 0))

    def is_night(self) -> bool:
        if not self.p.cfg.get("raise.night_pause"):
            return False
        sh, sm = parse_hhmm(self.p.cfg.get("raise.night_start"))
        eh, em = parse_hhmm(self.p.cfg.get("raise.night_end"))
        now = datetime.now()
        cur = now.hour * 60 + now.minute
        start, end = sh * 60 + sm, eh * 60 + em
        return start <= cur < end if start < end else (cur >= start or cur < end)

    def raise_one(self, cat_id: int, name: str = "") -> tuple[bool, str]:
        """Поднимает одну категорию, пишет raise_state."""
        jitter = int(self.p.cfg.get("raise.jitter_min")) * 60
        ok, text, wait = False, "", 3600
        if self.p.dry:
            log_info(f"[DRY-RUN] Поднятие категории {cat_id} {name}")
            ok, text, wait = True, "dry-run", 3600
        else:
            try:
                with self.p.fp_lock:
                    wait = self.p.c.account.raise_lots(cat_id)
                ok, text = True, "поднято"
                wait = int(wait) if wait else 3600
            except fp_exceptions.RaiseError as e:
                text = e.error_message or "ошибка поднятия"
                if e.wait_time is not None:
                    wait, ok = int(e.wait_time), True
                    text = f"ожидание: {text}"
                else:
                    wait = 600
            except Exception as e:
                text, wait = str(e)[:200], 600
        next_at = now_ts() + max(wait, wait + random.randint(-jitter, jitter) if jitter else wait)
        fails = 0 if ok else int(self.p.db.meta_get(f"raise_fail:{cat_id}", 0)) + 1
        self.p.db.meta_set(f"raise_fail:{cat_id}", fails)
        self.p.db.execute("INSERT INTO raise_state(category, next_at, last_ok, last_error) VALUES(?,?,?,?) "
                          "ON CONFLICT(category) DO UPDATE SET next_at=excluded.next_at, last_ok=COALESCE("
                          "excluded.last_ok, raise_state.last_ok), last_error=excluded.last_error",
                          (cat_id, next_at, now_ts() if ok else None, None if ok else text))
        if fails >= 3:
            self.p.alerts.send(f"🔄 Поднятие «{esc(name or cat_id)}»: {fails} неудачи подряд — {esc(text)}",
                               key=f"raise:{cat_id}")
        log_info(f"Поднятие {name or cat_id}: {text}; следующее через {fmt_duration(next_at - now_ts())}")
        return ok, text

    def step(self) -> int:
        """Один проход цикла; возвращает паузу до следующего прохода (с)."""
        if not self.p.cfg.get("raise.enabled"):
            return 30
        if self.is_night():
            return 300
        nearest = 600
        for cat_id, name in self.selected():
            if self.p.stop.is_set():
                break
            st = self.p.db.one("SELECT * FROM raise_state WHERE category=?", (cat_id,))
            if st and int(st["next_at"] or 0) > now_ts():
                nearest = min(nearest, int(st["next_at"]) - now_ts())
                continue
            self.raise_one(cat_id, name)
            time.sleep(2)
        return max(10, nearest)

    def raise_now(self) -> str:
        lines = []
        for cat_id, name in self.selected():
            ok, text = self.raise_one(cat_id, name)
            lines.append(f"{'✅' if ok else '❌'} {esc(name)}: {esc(text)}")
            time.sleep(2)
        return "\n".join(lines) or "Нет категорий с лотами плагина."

    def status_text(self) -> str:
        lines = [f"<b>🔄 Автоподнятие</b>: {'вкл' if self.p.cfg.get('raise.enabled') else 'выкл'}",
                 f"Ночная пауза: {'вкл' if self.p.cfg.get('raise.night_pause') else 'выкл'} "
                 f"({self.p.cfg.get('raise.night_start')}–{self.p.cfg.get('raise.night_end')}), "
                 f"сдвиг ±{self.p.cfg.get('raise.jitter_min')} мин"]
        if self.p.c.autoraise_enabled:
            lines.append("⚠️ В Cardinal включено собственное автоподнятие — возможен конфликт.")
        chosen = [int(x) for x in (self.p.cfg.get("raise.categories") or [])]
        for cat_id, name in self.categories():
            st = self.p.db.one("SELECT * FROM raise_state WHERE category=?", (cat_id,))
            mark = "☑️" if not chosen or cat_id in chosen else "⬜"
            nxt = fmt_duration(int(st["next_at"]) - now_ts()) if st and st["next_at"] else "—"
            err = f" ⚠️ {esc(st['last_error'][:60])}" if st and st["last_error"] else ""
            lines.append(f"{mark} {esc(name)}: следующее через {nxt}{err}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# K. SYNC: синхронизация лотов, обновление версий
# ═══════════════════════════════════════════════════════════════════════════════════════════════

class SyncManager:
    """Сопоставление лотов базы с лотами аккаунта FunPay без пересоздания."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.last_report = ""

    def check_version(self) -> None:
        prev = self.p.db.meta_get("plugin_version")
        if prev != VERSION:
            self.p.db.meta_set("plugin_version", VERSION)
            if prev:
                log_info(f"Плагин обновлён {prev} -> {VERSION}. Лоты не перевыставляются, выполняется синхронизация.")

    def fp_lots(self) -> list:
        """Все лоты аккаунта, включая неактивные (публичный профиль показывает только активные)."""
        with self.p.fp_lock:
            profile = self.p.c.account.get_user(self.p.c.account.id)
        public = [lot for lot in profile.get_lots() if lot.subcategory and
                  lot.subcategory.type is SubCategoryTypes.COMMON]
        nodes = {int(l.subcategory.id) for l in public}
        nodes |= {int(r["node_id"]) for r in self.p.db.query("SELECT DISTINCT node_id FROM lots WHERE node_id "
                                                             "IS NOT NULL")}
        result: dict[int, Any] = {}
        for node in sorted(nodes):
            try:
                with self.p.fp_lock:
                    mine = self.p.c.account.get_my_subcategory_lots(node)
                time.sleep(0.5)
            except Exception as e:
                log_warn(f"Синхронизация: лоты подкатегории {node} не получены ({e}), беру публичный профиль")
                mine = [l for l in public if int(l.subcategory.id) == node]
            sub = None
            for lot in mine:
                if lot.subcategory is None:
                    sub = sub or self.p.c.account.get_subcategory(SubCategoryTypes.COMMON, node)
                    lot.subcategory = sub
                if lot.subcategory is not None:
                    result[int(lot.id)] = lot
        return list(result.values())

    def run(self) -> str:
        """Синхронизация; возвращает текстовый отчёт."""
        fp = self.fp_lots()
        fp_by_id = {int(x.id): x for x in fp}
        lots = self.p.db.query("SELECT * FROM lots")
        respect = self.p.cfg.get("respect_manual_edits")
        used: set[int] = {int(l["fp_lot_id"]) for l in lots if l["fp_lot_id"] and int(l["fp_lot_id"]) in fp_by_id}
        rep = {"fp": len(fp), "matched": 0, "relinked": 0, "manual": 0, "lost": 0, "restored": 0}
        fetches = 0
        for lot in lots:
            fid = int(lot["fp_lot_id"]) if lot["fp_lot_id"] else None
            if fid and fid in fp_by_id:
                x = fp_by_id[fid]
                rep["matched"] += 1
                upd: dict = {}
                if lot["lost"]:
                    upd["lost"] = 0
                    rep["restored"] += 1
                if not lot["node_id"]:
                    upd["node_id"] = x.subcategory.id
                if lot["title"] and norm_text(x.description) != norm_text(lot["title"]) and respect \
                        and not lot["manual_edit"]:
                    upd["manual_edit"] = 1
                    rep["manual"] += 1
                if upd:
                    sets = ", ".join(f"{k}=?" for k in upd)
                    self.p.db.execute(f"UPDATE lots SET {sets}, updated_at=? WHERE id=?",
                                      list(upd.values()) + [now_ts(), lot["id"]])
                continue
            if not fid and lot["lost"] == 0 and not lot["template_id"]:
                continue
            found = None
            for x in fp:
                if int(x.id) in used:
                    continue
                if lot["node_id"] and x.subcategory.id != int(lot["node_id"]):
                    continue
                if lot["title"] and norm_text(x.description) == norm_text(lot["title"]):
                    found = x
                    break
            if not found and lot["supplier_id"] and fetches < 20:
                marker = MasterLot.marker(lot["supplier_id"], lot["service_id"], int(lot["pack_qty"] or 0))
                for x in fp:
                    if int(x.id) in used or (lot["node_id"] and x.subcategory.id != int(lot["node_id"])):
                        continue
                    if fetches >= 20:
                        break
                    fetches += 1
                    try:
                        with self.p.fp_lock:
                            lf = self.p.c.account.get_lot_fields(int(x.id))
                        time.sleep(0.5)
                    except Exception:
                        continue
                    blob = f"{lf.description_ru}\n{lf.description_en}\n" + "\n".join(lf.secrets)
                    if re.search(re.escape(marker) + r"(?![\d-])", blob):
                        found = x
                        break
            if found:
                used.add(int(found.id))
                self.p.db.execute("UPDATE lots SET fp_lot_id=?, node_id=?, lost=0, updated_at=? WHERE id=?",
                                  (int(found.id), found.subcategory.id, now_ts(), lot["id"]))
                rep["relinked"] += 1
            elif fid and not lot["lost"]:
                self.p.db.execute("UPDATE lots SET lost=1, updated_at=? WHERE id=?", (now_ts(), lot["id"]))
                rep["lost"] += 1
        foreign = len([x for x in fp if int(x.id) not in used])
        self.last_report = (f"<b>🔁 Синхронизация</b>\nЛотов на FP: {rep['fp']}\nСопоставлено: {rep['matched']}\n"
                            f"Перепривязано (новый id): {rep['relinked']}\nПомечено «ручные правки»: {rep['manual']}\n"
                            f"Потеряно: {rep['lost']}\nВосстановлено из потерянных: {rep['restored']}\n"
                            f"Чужих лотов (не трогаются): {foreign}")
        self.p.db.meta_set("last_sync", now_ts())
        log_info(re.sub(r"<[^>]+>", "", self.last_report).replace("\n", "; "))
        return self.last_report


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# L. TRANSFER: экспорт/импорт/бэкапы («Перенос лотов»)
# ═══════════════════════════════════════════════════════════════════════════════════════════════

def canonical_json(data: Any) -> str:
    return json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def pw_encrypt(text: str, password: str) -> str:
    """Шифрование паролем: PBKDF2-SHA256 + потоковый шифр на SHA-256 + HMAC (без внешних библиотек)."""
    salt, nonce = os.urandom(16), os.urandom(16)
    key = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 200_000, 32)
    raw = text.encode("utf-8")
    stream = b"".join(hashlib.sha256(key + nonce + i.to_bytes(4, "big")).digest()
                      for i in range(len(raw) // 32 + 1))
    ct = bytes(a ^ b for a, b in zip(raw, stream))
    mac = hmac.new(key, nonce + ct, hashlib.sha256).digest()
    return base64.b64encode(salt + nonce + mac + ct).decode()


def pw_decrypt(blob: str, password: str) -> str:
    data = base64.b64decode(blob.encode())
    salt, nonce, mac, ct = data[:16], data[16:32], data[32:64], data[64:]
    key = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 200_000, 32)
    if not hmac.compare_digest(mac, hmac.new(key, nonce + ct, hashlib.sha256).digest()):
        raise ValueError("неверный пароль")
    stream = b"".join(hashlib.sha256(key + nonce + i.to_bytes(4, "big")).digest()
                      for i in range(len(ct) // 32 + 1))
    return bytes(a ^ b for a, b in zip(ct, stream)).decode("utf-8")


def migrate_export_v0_to_v1(doc: dict) -> dict:
    """v0: данные лежали на верхнем уровне без format_version/checksum."""
    data = {k: doc.get(k, []) for k in ("suppliers", "templates", "lots", "lot_services", "service_stats", "promo",
                                         "blacklist")}
    data["settings"] = doc.get("settings", {})
    return {"format_version": 1, "plugin_version": doc.get("plugin_version", "0"),
            "schema_version": doc.get("schema_version", 1), "exported_at": doc.get("exported_at", ""),
            "checksum": hashlib.sha256(canonical_json(data).encode()).hexdigest(), "data": data}


EXPORT_MIGRATIONS: dict[int, Callable[[dict], dict]] = {0: migrate_export_v0_to_v1}


class TransferError(Exception):
    pass


class Transfer:
    """Экспорт/импорт настроек, поставщиков, шаблонов и привязок лотов."""

    def __init__(self, p: "AutoSMM"):
        self.p = p

    def export(self, include_keys: bool = False, include_stats: bool = False, include_bl: bool = False,
               password: str = "") -> tuple[str, int]:
        """Создаёт файл экспорта; возвращает (путь, число активных заказов, не вошедших в экспорт)."""
        db = self.p.db
        suppliers = []
        for r in db.query("SELECT * FROM suppliers ORDER BY id"):
            item = {"id": r["id"], "name": r["name"], "preset": r["preset"], "currency": r["currency"],
                    "enabled": r["enabled"], "priority": r["priority"], "select_mode": r["select_mode"],
                    "profile": json.loads(r["profile_json"] or "{}")}
            if include_keys and password:
                key = db.dec(r["api_key_enc"])
                if key:
                    item["api_key_encrypted"] = pw_encrypt(key, password)
            suppliers.append(item)
        data = {
            "settings": self.p.cfg.data,
            "suppliers": suppliers,
            "templates": db.query("SELECT * FROM templates ORDER BY id"),
            "lots": db.query("SELECT id, fp_lot_id, node_id, template_id, supplier_id, service_id, pack_qty, title, mode,"
                             " margin_override, manual_price, enabled, manual_edit, price FROM lots ORDER BY id"),
            "lot_services": db.query("SELECT * FROM lot_services"),
            "service_stats": db.query("SELECT * FROM service_stats") if include_stats else [],
            "promo": db.query("SELECT * FROM promo") if include_bl else [],
            "blacklist": db.query("SELECT * FROM blacklist") if include_bl else [],
        }
        doc = {"format_version": EXPORT_FORMAT_VERSION, "plugin_version": VERSION, "schema_version": SCHEMA_VERSION,
               "exported_at": datetime.now().isoformat(timespec="seconds"),
               "checksum": hashlib.sha256(canonical_json(data).encode()).hexdigest(), "data": data}
        ensure_dirs()
        name = f"autosmmway_export_{datetime.now():%Y%m%d_%H%M}_v{VERSION}.json"
        path = os.path.join(EXPORT_DIR, name)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(doc, f, ensure_ascii=False, indent=1)
        if os.path.getsize(path) > 10 * 1024 * 1024:
            zpath = path[:-5] + ".zip"
            with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
                z.write(path, name)
            os.remove(path)
            path = zpath
        active = int(db.scalar(f"SELECT COUNT(*) FROM orders WHERE status IN ({','.join('?' * len(ACTIVE_ORDER_STATUSES))})",
                               ACTIVE_ORDER_STATUSES, 0))
        log_info(f"Экспорт создан: {os.path.basename(path)} (ключи: {'да' if include_keys and password else 'нет'})")
        return path, active

    def load(self, path: str) -> dict:
        """Читает и проверяет файл экспорта; старые форматы мигрируются."""
        try:
            if path.endswith(".zip"):
                with zipfile.ZipFile(path) as z:
                    names = [n for n in z.namelist() if n.endswith(".json")]
                    if not names:
                        raise TransferError("в архиве нет JSON-файла")
                    raw = z.read(names[0]).decode("utf-8")
            else:
                with open(path, "r", encoding="utf-8") as f:
                    raw = f.read()
            doc = json.loads(raw)
        except TransferError:
            raise
        except Exception as e:
            raise TransferError(f"файл не является корректным JSON: {e}")
        if not isinstance(doc, dict):
            raise TransferError("неверная структура файла")
        fv = int(doc.get("format_version", 0) or 0)
        if fv > EXPORT_FORMAT_VERSION:
            raise TransferError(f"файл создан более новой версией плагина ({doc.get('plugin_version')}), "
                                f"формат {fv} > {EXPORT_FORMAT_VERSION}. Обновите плагин.")
        while fv < EXPORT_FORMAT_VERSION:
            doc = EXPORT_MIGRATIONS[fv](doc)
            fv = int(doc["format_version"])
        if int(doc.get("schema_version", 0) or 0) > SCHEMA_VERSION:
            raise TransferError("файл создан с более новой схемой базы. Обновите плагин.")
        data = doc.get("data")
        if not isinstance(data, dict):
            raise TransferError("нет раздела data")
        if hashlib.sha256(canonical_json(data).encode()).hexdigest() != doc.get("checksum"):
            raise TransferError("контрольная сумма не совпадает — файл повреждён или изменён")
        return doc

    def _match_supplier(self, item: dict) -> Optional[dict]:
        base = (item.get("profile") or {}).get("base_url")
        for r in self.p.sup.list():
            prof = json.loads(r["profile_json"] or "{}")
            if r["name"] == item.get("name") and prof.get("base_url") == base:
                return r
        return None

    def preview(self, doc: dict) -> tuple[str, dict]:
        """Превью импорта без изменений."""
        data = doc["data"]
        try:
            fp_ids = {int(x.id) for x in self.p.sync.fp_lots()}
        except Exception as e:
            log_warn(f"Превью импорта: не удалось получить лоты FP: {e}")
            fp_ids = set()
        lots = data.get("lots") or []
        on_fp = [l for l in lots if l.get("fp_lot_id") and int(l["fp_lot_id"]) in fp_ids]
        in_db = 0
        for l in lots:
            if (l.get("fp_lot_id") and self.p.db.one("SELECT 1 FROM lots WHERE fp_lot_id=?", (l["fp_lot_id"],))):
                in_db += 1
        missing = [l for l in lots if not (l.get("fp_lot_id") and int(l["fp_lot_id"]) in fp_ids)]
        creatable = [l for l in missing if l.get("template_id") and l.get("supplier_id")]
        sup_new = sum(1 for s in data.get("suppliers") or [] if not self._match_supplier(s))
        tpl_names = {t["name"] for t in self.p.ml.templates()}
        tpl_new = sum(1 for t in data.get("templates") or [] if t.get("name") not in tpl_names)
        conflicts = [k for k, v in (data.get("settings") or {}).items()
                     if k in self.p.cfg.data and self.p.cfg.data.get(k) != v]
        no_keys = sum(1 for s in data.get("suppliers") or [] if not s.get("api_key_encrypted")
                      and not self._match_supplier(s))
        stats = {"lots": len(lots), "on_fp": len(on_fp), "bind": len(on_fp), "create": len(creatable),
                 "skip": len(missing) - len(creatable), "in_db": in_db, "suppliers": len(data.get("suppliers") or []),
                 "sup_new": sup_new, "templates": len(data.get("templates") or []), "tpl_new": tpl_new,
                 "conflicts": conflicts, "no_keys": no_keys,
                 "has_keys": any(s.get("api_key_encrypted") for s in data.get("suppliers") or [])}
        text = (f"<b>Превью импорта</b> (файл v{esc(doc.get('plugin_version'))}, {esc(doc.get('exported_at'))})\n"
                f"Лотов в файле: {stats['lots']}\nНайдено на FP: {stats['on_fp']}\n"
                f"Будет привязано: {stats['bind']} (уже в базе: {stats['in_db']})\n"
                f"Будет создано (режим «создать недостающие»): {stats['create']}\n"
                f"Будет пропущено: {stats['skip']}\n"
                f"Поставщиков: {stats['suppliers']} (новых {stats['sup_new']}, без ключа {stats['no_keys']})\n"
                f"Шаблонов: {stats['templates']} (новых {stats['tpl_new']})\n"
                f"Конфликтов настроек: {len(conflicts)}" + (f" ({esc(', '.join(conflicts[:10]))})" if conflicts else ""))
        return text, stats

    def apply(self, doc: dict, mode: str, conflict: str, password: str = "") -> dict:
        """mode: bind | bind_create | settings; conflict: keep | file. Делает автобэкап перед применением."""
        backup = self.p.db.backup("pre_import")
        self.p.db.meta_set("last_import_backup", backup)
        with open(backup + ".config.json", "w", encoding="utf-8") as f:
            json.dump(self.p.cfg.data, f, ensure_ascii=False)
        data = doc["data"]
        rep = {"bound": 0, "created": 0, "skipped": 0, "errors": [], "suppliers": 0, "templates": 0, "settings": 0}
        # Настройки
        for k, v in (data.get("settings") or {}).items():
            if k == "admin_ids" and v == []:
                continue
            if k not in self.p.cfg.data or conflict == "file":
                if self.p.cfg.data.get(k) != v:
                    self.p.cfg.data[k] = v
                    rep["settings"] += 1
        self.p.cfg.validate()
        self.p.cfg.save()
        # Поставщики
        sup_map: dict[int, int] = {}
        for s in data.get("suppliers") or []:
            local = self._match_supplier(s)
            key = ""
            if s.get("api_key_encrypted") and password:
                try:
                    key = pw_decrypt(s["api_key_encrypted"], password)
                except Exception as e:
                    rep["errors"].append(f"ключ {s.get('name')}: {e}")
            if local:
                sup_map[int(s["id"])] = local["id"]
                if conflict == "file":
                    prof = s.get("profile") or {}
                    prof["name"] = s.get("name")
                    self.p.sup.update_profile(local["id"], prof)
                    self.p.sup.set_field(local["id"], "priority", int(s.get("priority") or 100))
                if key:
                    self.p.sup.set_key(local["id"], key)
            else:
                prof = s.get("profile") or {}
                prof["name"] = s.get("name")
                new_id = self.p.sup.add(prof, key, enabled=bool(s.get("enabled")), priority=int(s.get("priority") or
                                                                                                 100),
                                        needs_key=not key)
                if s.get("select_mode"):
                    self.p.sup.set_field(new_id, "select_mode", s["select_mode"])
                sup_map[int(s["id"])] = new_id
                rep["suppliers"] += 1
        # Шаблоны
        tpl_map: dict[int, int] = {}
        for t in data.get("templates") or []:
            local = self.p.db.one("SELECT * FROM templates WHERE name=?", (t.get("name"),))
            fields = {k: t.get(k) for k in MasterLot.TEMPLATE_FIELDS}
            if local:
                tpl_map[int(t["id"])] = local["id"]
                if conflict == "file":
                    self.p.ml.save_template(fields, local["id"])
            else:
                tpl_map[int(t["id"])] = self.p.ml.save_template(fields)
                rep["templates"] += 1
        if mode == "settings":
            return rep
        try:
            fp_ids = {int(x.id) for x in self.p.sync.fp_lots()}
        except Exception as e:
            rep["errors"].append(f"не удалось получить лоты FP: {e}")
            fp_ids = set()
        lot_map: dict[int, int] = {}
        for l in data.get("lots") or []:
            try:
                tid = tpl_map.get(int(l["template_id"])) if l.get("template_id") else None
                sid = sup_map.get(int(l["supplier_id"])) if l.get("supplier_id") else None
                pack = int(l.get("pack_qty") or 0)
                local = None
                if l.get("fp_lot_id"):
                    local = self.p.db.one("SELECT * FROM lots WHERE fp_lot_id=?", (int(l["fp_lot_id"]),))
                if not local and tid and sid:
                    local = self.p.db.one("SELECT * FROM lots WHERE template_id=? AND supplier_id=? AND service_id=? "
                                          "AND pack_qty=?", (tid, sid, str(l.get("service_id")), pack))
                if local:
                    lot_map[int(l["id"])] = local["id"]
                    if conflict == "file":
                        self.p.db.execute("UPDATE lots SET margin_override=?, manual_price=?, enabled=?, mode=?, "
                                          "updated_at=? WHERE id=?", (l.get("margin_override"), l.get("manual_price"),
                                                                      int(l.get("enabled", 1)), l.get("mode"),
                                                                      now_ts(), local["id"]))
                    rep["bound"] += 1
                    continue
                on_fp = l.get("fp_lot_id") and int(l["fp_lot_id"]) in fp_ids
                if not on_fp and mode != "bind_create":
                    rep["skipped"] += 1
                    rep["errors"].append(f"лот {l.get('fp_lot_id')}: нет на FP")
                    continue
                if not on_fp and not (tid and sid):
                    rep["skipped"] += 1
                    rep["errors"].append(f"лот {l.get('title', '')[:40]}: нет шаблона/поставщика для создания")
                    continue
                ts = now_ts()
                new_id = self.p.db.execute(
                    "INSERT INTO lots(fp_lot_id, node_id, template_id, title, mode, margin_override, manual_price, "
                    "enabled, lost, created_at, updated_at, pack_qty, supplier_id, service_id, price, manual_edit) "
                    "VALUES(?,?,?,?,?,?,?,?,0,?,?,?,?,?,?,?)",
                    (int(l["fp_lot_id"]) if on_fp else None, l.get("node_id"), tid, l.get("title"), l.get("mode"),
                     l.get("margin_override"), l.get("manual_price"), int(l.get("enabled", 1)), ts, ts, pack, sid,
                     str(l.get("service_id")) if l.get("service_id") is not None else None, l.get("price"),
                     int(l.get("manual_edit") or 0)))
                lot_map[int(l["id"])] = new_id
                if on_fp:
                    rep["bound"] += 1
                else:
                    lot_map[int(l["id"])] = new_id
                    rep["created_pending"] = rep.get("created_pending", 0) + 1
            except Exception as e:
                rep["errors"].append(f"лот {l.get('id')}: {e}")
        for ls in data.get("lot_services") or []:
            lid = lot_map.get(int(ls["lot_id"]))
            sid = sup_map.get(int(ls["supplier_id"]))
            if lid and sid:
                self.p.db.execute("INSERT OR IGNORE INTO lot_services(lot_id, supplier_id, service_id, is_primary, "
                                  "position) VALUES(?,?,?,?,?)", (lid, sid, str(ls["service_id"]),
                                                                  int(ls.get("is_primary") or 0),
                                                                  int(ls.get("position") or 0)))
        verb = "INSERT OR REPLACE" if conflict == "file" else "INSERT OR IGNORE"
        for st in data.get("service_stats") or []:
            sid = sup_map.get(int(st["supplier_id"]))
            if sid:
                self.p.db.execute(f"{verb} INTO service_stats(supplier_id, service_id, orders_total, completed, partial,"
                                  f" canceled, failed, refills, avg_seconds, rating, updated_at) "
                                  f"VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                                  (sid, str(st["service_id"]), st.get("orders_total"), st.get("completed"),
                                   st.get("partial"), st.get("canceled"), st.get("failed"), st.get("refills"),
                                   st.get("avg_seconds"), st.get("rating"), st.get("updated_at")))
        for pr in data.get("promo") or []:
            self.p.db.execute(f"{verb} INTO promo(code, buyer, percent, used, ts) VALUES(?,?,?,?,?)",
                              (pr["code"], pr.get("buyer"), pr.get("percent"), pr.get("used"), pr.get("ts")))
        for b in data.get("blacklist") or []:
            self.p.db.execute(f"{verb} INTO blacklist(buyer, reason, ts) VALUES(?,?,?)",
                              (b["buyer"], b.get("reason"), b.get("ts")))
        if mode == "bind_create":
            pending = self.p.db.query("SELECT * FROM lots WHERE fp_lot_id IS NULL AND template_id IS NOT NULL AND "
                                      "supplier_id IS NOT NULL AND lost=0")
            for lot in pending:
                t = self.p.ml.template(lot["template_id"])
                svc = self.p.sup.service(lot["supplier_id"], lot["service_id"])
                if not svc:
                    try:
                        self.p.sup.refresh_catalog(lot["supplier_id"])
                        svc = self.p.sup.service(lot["supplier_id"], lot["service_id"])
                    except SupplierError as e:
                        rep["errors"].append(f"каталог поставщика {lot['supplier_id']}: {e.message}")
                if not t or not svc:
                    rep["skipped"] += 1
                    rep["errors"].append(f"лот {lot['title'] or lot['id']}: нет шаблона/услуги в каталоге")
                    continue
                try:
                    res, _lid, _info = self.p.ml.upsert(t, lot["supplier_id"], svc, int(lot["pack_qty"] or 0))
                    rep["created" if res == "created" else "skipped"] += 1
                    time.sleep(float(self.p.cfg.get("fp_pause")))
                except Exception as e:
                    rep["errors"].append(f"создание {lot['title'] or lot['id']}: {str(e)[:120]}")
        rep.pop("created_pending", None)
        self.p.sup.invalidate()
        log_info(f"Импорт применён: {rep['bound']} привязано, {rep['created']} создано, {rep['skipped']} пропущено")
        return rep

    def rollback(self) -> str:
        path = self.p.db.meta_get("last_import_backup")
        if not path or not os.path.exists(path):
            return "Бэкап последнего импорта не найден."
        self.p.db.restore(path)
        cfg_path = path + ".config.json"
        if os.path.exists(cfg_path):
            with open(cfg_path, "r", encoding="utf-8") as f:
                self.p.cfg.data = deep_merge(DEFAULTS, json.load(f))
            self.p.cfg.validate()
            self.p.cfg.save()
        self.p.db.meta_set("last_import_backup", "")
        self.p.sup.invalidate()
        return "Импорт откатан: база и настройки восстановлены из автобэкапа."


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# M. TELEGRAM UI: меню, колбэки, ввод текста, пагинация
# ═══════════════════════════════════════════════════════════════════════════════════════════════

TEMPLATE_STEPS: list[tuple[str, str, bool]] = [
    ("name", "Название шаблона (для себя)", True),
    ("title_ru", "Заголовок лота RU. Можно использовать кодовые слова, например:\n"
                 "<code>{platform} {service_name} — {quantity} шт. {badge}</code>", True),
    ("title_en", "Заголовок лота EN (или «-», чтобы взять RU)", False),
    ("desc_ru", "Описание лота RU (кодовые слова в фигурных скобках)", True),
    ("desc_en", "Описание лота EN (или «-»)", False),
    ("category_node", "ID подкатегории FunPay (node) — число из ссылки funpay.com/lots/<b>NODE</b>/", True),
    ("price_mode", "Режим цены", True),
    ("quantity_pack", "Пакеты количества через запятую, например: 100, 500, 1000", True),
    ("secrets_text", "Текст автовыдачи (отправляется после оплаты) или «-»", False),
    ("autoreply_text", "Текст автоответа при запуске заказа (кодовые слова сообщений) или «-»", False),
]
TEMPLATE_FIELD_TITLES = {k: v.split("\n")[0].split(".")[0] for k, v, _r in TEMPLATE_STEPS}
PRICE_MODE_TITLES = {"per_1000": "за 1000 (кол-во = шт. × 1000)", "pack": "фиксированный пакет",
                     "per_1": "за 1 шт. (покупатель выбирает количество)"}

SUPPLIER_EDIT_FIELDS: list[tuple[str, str, str]] = [
    ("name", "Название", "str"), ("base_url", "Base URL", "str"), ("api_key", "API-ключ", "secret"),
    ("method", "HTTP-метод (GET/POST)", "str"), ("request_format", "Формат (form/json)", "str"),
    ("currency", "Валюта", "str"), ("rate_unit", "Цена за N единиц", "int"), ("timeout", "Таймаут, с", "int"),
    ("retries", "Ретраи", "int"), ("rate_limit_per_sec", "Запросов/с", "float"), ("auth", "auth (JSON)", "json"),
    ("endpoints", "endpoints (JSON)", "json"), ("params_map", "params_map (JSON)", "json"),
    ("response_map", "response_map (JSON)", "json"), ("status_map", "status_map (JSON)", "json"),
]


class TelegramUI:
    """Inline-интерфейс плагина. Доступ только для admin_ids, проверка в каждом колбэке."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.c = p.c
        self.tg = p.c.telegram
        self.bot = self.tg.bot if self.tg else None
        self.sessions: dict[int, dict] = {}
        self._cbmap: dict[str, list[str]] = {}
        self._cb_lock = threading.Lock()

    # ── инфраструктура ──
    def register(self) -> None:
        if not self.tg:
            log_warn("Telegram отключён в Cardinal — интерфейс плагина недоступен.")
            return
        self.tg.cbq_handler(self.on_callback, lambda c: c.data.startswith(f"{CB_PREFIX}:"))
        self.tg.cbq_handler(self.open_from_settings, lambda c: c.data.startswith(f"{CBT.PLUGIN_SETTINGS}:{UUID}"))
        self.tg.msg_handler(self.cmd_menu, commands=["autosmm"])
        self.tg.msg_handler(self.on_text, content_types=["text"],
                            func=lambda m: self.tg.check_state(m.chat.id, m.from_user.id, STATE_INPUT))
        self.tg.file_handler(STATE_FILE, self.on_file)
        self.c.add_telegram_commands(UUID, [("autosmm", "меню AutoSMMway", True)])

    def cb(self, *parts: Any) -> str:
        data = ":".join([CB_PREFIX] + [str(x) for x in parts])
        if len(data.encode()) <= 64:
            return data
        token = hashlib.md5(data.encode()).hexdigest()[:12]
        with self._cb_lock:
            self._cbmap[token] = [str(x) for x in parts]
            if len(self._cbmap) > 5000:
                for k in list(self._cbmap)[:1000]:
                    self._cbmap.pop(k, None)
        return f"{CB_PREFIX}:~:{token}"

    def is_admin(self, uid: int) -> bool:
        return int(uid) in self.p.cfg.admin_ids(self.c)

    def sess(self, uid: int) -> dict:
        return self.sessions.setdefault(int(uid), {})

    @staticmethod
    def nav(kb: K, back: Optional[str]) -> K:
        row = []
        if back:
            row.append(B("◀️ Назад", callback_data=back))
        row.append(B("🏠 В главное меню", callback_data=f"{CB_PREFIX}:m"))
        kb.row(*row)
        return kb

    def paginate(self, kb: K, items: list, page: int, make_btn: Callable[[Any], B], page_cb: Callable[[int], str]
                 ) -> int:
        pages = max(1, (len(items) + PAGE_SIZE - 1) // PAGE_SIZE)
        page = max(0, min(int(page), pages - 1))
        for item in items[page * PAGE_SIZE:(page + 1) * PAGE_SIZE]:
            kb.row(make_btn(item))
        if pages > 1:
            kb.row(B("⬅️", callback_data=page_cb((page - 1) % pages)),
                   B(f"{page + 1}/{pages}", callback_data=self.cb("noop")),
                   B("➡️", callback_data=page_cb((page + 1) % pages)))
        return page

    def show(self, target: Any, text: str, kb: Optional[K] = None) -> None:
        """Редактирует сообщение (колбэк или (chat, msg_id)); при невозможности — отправляет новое."""
        if not self.bot:
            return
        if len(text) > 4000:
            text = text[:3990] + "\n…"
        if isinstance(target, CallbackQuery):
            chat_id, mid = target.message.chat.id, target.message.id
        elif isinstance(target, tuple):
            chat_id, mid = target
        else:
            chat_id, mid = target, None
        if mid:
            try:
                self.bot.edit_message_text(text, chat_id, mid, parse_mode="HTML", reply_markup=kb,
                                           disable_web_page_preview=True)
                return
            except Exception as e:
                if "message is not modified" in str(e):
                    return
        try:
            self.bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)
        except Exception:
            log_error("Telegram: не удалось отправить сообщение", exc=True)

    def toast(self, call: CallbackQuery, text: str = "", alert: bool = False) -> None:
        try:
            self.bot.answer_callback_query(call.id, text[:190], show_alert=alert)
        except Exception:
            pass

    def ask(self, target: Any, user_id: int, prompt: str, kind: str, data: Optional[dict] = None,
            back: Optional[str] = None, file: bool = False) -> None:
        """Запрашивает ввод текста/файла с кнопкой «Отмена»."""
        if isinstance(target, CallbackQuery):
            chat_id, mid = target.message.chat.id, target.message.id
        else:
            chat_id, mid = target
        kb = K().row(B("❌ Отмена", callback_data=self.cb("x")))
        self.show((chat_id, mid), prompt, kb)
        payload = dict(data or {})
        payload.update({"kind": kind, "back": back or self.cb("m")})
        self.tg.set_state(chat_id, mid, user_id, STATE_FILE if file else STATE_INPUT, payload)

    def bg(self, target: Any, fn: Callable[[], tuple[str, Optional[K]]], wait_text: str = "⏳ Выполняю…") -> None:
        """Выполняет долгую операцию в отдельном потоке."""
        if isinstance(target, CallbackQuery):
            target = (target.message.chat.id, target.message.id)
        self.show(target, wait_text)

        def run() -> None:
            try:
                text, kb = fn()
            except Exception as e:
                log_error(f"UI bg: {e}", exc=True)
                text, kb = f"❌ Ошибка: {esc(str(e)[:300])}", self.nav(K(), None)
            self.show(target, text, kb)

        threading.Thread(target=run, daemon=True, name="asm-ui-bg").start()

    def send_document(self, chat_id: int, path: str, caption: str = "") -> None:
        with open(path, "rb") as f:
            self.bot.send_document(chat_id, f, caption=caption[:1000], parse_mode="HTML",
                                   visible_file_name=os.path.basename(path))

    def download(self, m: Message, name: str) -> str:
        info = self.bot.get_file(m.document.file_id)
        data = self.bot.download_file(info.file_path)
        ensure_dirs()
        path = os.path.join(TMP_DIR, f"{now_ts()}_{re.sub(r'[^A-Za-z0-9_.-]', '_', name)}")
        with open(path, "wb") as f:
            f.write(data)
        return path

    # ── входные точки ──
    def cmd_menu(self, m: Message) -> None:
        if not self.is_admin(m.from_user.id):
            return
        text, kb = self.scr_main(m.from_user.id)
        self.show(m.chat.id, text, kb)

    def open_from_settings(self, call: CallbackQuery) -> None:
        if not self.is_admin(call.from_user.id):
            return self.toast(call, "Нет доступа", True)
        parts = call.data.split(":")
        self.sess(call.from_user.id)["plugins_offset"] = parts[2] if len(parts) > 2 and parts[2].isdigit() else "0"
        text, kb = self.scr_main(call.from_user.id)
        self.show(call, text, kb)
        self.toast(call)

    def on_callback(self, call: CallbackQuery) -> None:
        if not self.is_admin(call.from_user.id):
            return self.toast(call, "Нет доступа", True)
        parts = call.data.split(":")[1:]
        if parts and parts[0] == "~":
            parts = self._cbmap.get(parts[1]) if len(parts) > 1 else None
            if not parts:
                self.toast(call, "Кнопка устарела, откройте меню заново", True)
                return
        action, args = parts[0], parts[1:]
        handler = getattr(self, f"r_{action}", None)
        if not handler:
            return self.toast(call, "Неизвестная команда")
        try:
            result = handler(call, *args)
            if isinstance(result, tuple):
                self.show(call, *result)
            self.toast(call)
        except Exception as e:
            log_error(f"UI {action}: {e}", exc=True)
            self.toast(call, f"Ошибка: {str(e)[:150]}", True)

    def on_text(self, m: Message) -> None:
        if not self.is_admin(m.from_user.id):
            return
        st = self.tg.get_state(m.chat.id, m.from_user.id)
        if not st:
            return
        data, mid = st["data"], st["mid"]
        self.tg.clear_state(m.chat.id, m.from_user.id)
        try:
            self.bot.delete_message(m.chat.id, m.id)
        except Exception:
            pass
        handler = getattr(self, f"i_{data['kind']}", None)
        if not handler:
            return
        try:
            result = handler((m.chat.id, mid), m.from_user.id, (m.text or "").strip(), data)
            if isinstance(result, tuple):
                self.show((m.chat.id, mid), *result)
        except Exception as e:
            log_error(f"UI input {data['kind']}: {e}", exc=True)
            self.show((m.chat.id, mid), f"❌ Ошибка: {esc(str(e)[:300])}", self.nav(K(), data.get("back")))

    def on_file(self, m: Message) -> None:
        if not self.is_admin(m.from_user.id) or not m.document:
            return
        st = self.tg.get_state(m.chat.id, m.from_user.id)
        if not st:
            return
        data, mid = st["data"], st["mid"]
        self.tg.clear_state(m.chat.id, m.from_user.id)
        handler = getattr(self, f"f_{data['kind']}", None)
        if not handler:
            return
        try:
            path = self.download(m, m.document.file_name or "file.json")
            result = handler((m.chat.id, mid), m.from_user.id, path, data)
            if isinstance(result, tuple):
                self.show((m.chat.id, mid), *result)
        except Exception as e:
            log_error(f"UI file {data['kind']}: {e}", exc=True)
            self.show((m.chat.id, mid), f"❌ Ошибка: {esc(str(e)[:300])}", self.nav(K(), data.get("back")))

    def r_noop(self, call: CallbackQuery, *args: str) -> None:
        return None

    def r_x(self, call: CallbackQuery, *args: str) -> tuple:
        st = self.tg.get_state(call.message.chat.id, call.from_user.id)
        back = (st or {}).get("data", {}).get("back")
        self.tg.clear_state(call.message.chat.id, call.from_user.id)
        if back:
            parts = back.split(":")[1:]
            if parts and parts[0] == "~":
                parts = self._cbmap.get(parts[1], ["m"])
            handler = getattr(self, f"r_{parts[0]}", None)
            if handler:
                res = handler(call, *parts[1:])
                if isinstance(res, tuple):
                    return res
                return None
        return self.scr_main(call.from_user.id)

    def order_kb(self, oid: int) -> K:
        return K().row(B("🧾 Открыть заказ", callback_data=self.cb("od", oid)))

    # ── главное меню ──
    def setup_steps(self) -> list[tuple[str, bool, str]]:
        """Шаги быстрой настройки: (название, выполнен, callback)."""
        p = self.p
        has_sup = any(not s["needs_key"] for s in p.sup.list(enabled_only=True))
        lots = int(p.db.scalar("SELECT COUNT(*) FROM lots WHERE fp_lot_id IS NOT NULL AND lost=0", (), 0))
        return [
            ("Подключить сайт-поставщика", has_sup, self.cb("go1")),
            ("Выбрать наценку", bool(p.db.meta_get("setup_margin")), self.cb("go2")),
            ("Выставить лоты", lots > 0, self.cb("go3")),
            ("Включить боевой режим", not p.dry, self.cb("go4")),
        ]

    # ── быстрая настройка ──
    def r_go(self, call: CallbackQuery, *args: str) -> tuple:
        steps = self.setup_steps()
        lines = ["<b>🚀 Быстрая настройка</b>", "Пройдите шаги по порядку — это займёт пару минут.\n"]
        kb = K()
        nxt = None
        for i, (title, ok, cbd) in enumerate(steps, 1):
            lines.append(f"{'✅' if ok else '⬜'} {i}. {title}")
            if not ok and nxt is None:
                nxt = (i, title, cbd)
            kb.row(B(f"{'✅' if ok else '⬜'} {i}. {title}", callback_data=cbd))
        if nxt:
            lines.append(f"\n➡️ Следующий шаг: <b>{nxt[1]}</b>")
        else:
            lines.append("\n🎉 Всё готово! Плагин сам принимает заказы, отправляет их поставщику, следит за ценами "
                         "и возвращает деньги, если что-то пошло не так. Вам остаётся пополнять баланс сайта.")
        return "\n".join(lines), self.nav(kb, self.cb("m"))

    def r_go1(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        kb.row(B("⭐ SMMway — нужен только ключ", callback_data=self.cb("qa", "smmway")))
        kb.row(B("🌐 Другая SMM-панель (ссылка + ключ)", callback_data=self.cb("qa", "smm_v2")))
        kb.row(B("🛠 Свой API — ручная настройка", callback_data=self.cb("sa")))
        return ("<b>Шаг 1. Подключить сайт</b>\nОткуда брать услуги? Большинство SMM-панелей работают по одному "
                "стандарту — достаточно адреса API и ключа из личного кабинета сайта (раздел «API»)."), \
            self.nav(kb, self.cb("go"))

    def r_qa(self, call: CallbackQuery, preset: str) -> None:
        self.sess(call.from_user.id)["qa"] = {"preset": preset}
        if preset == "smmway":
            url = PRESETS["smmway"]["profile"]["base_url"]
            self.ask(call, call.from_user.id, f"Пришлите <b>API-ключ SMMway</b> (личный кабинет → API).\n"
                                              f"Сообщение с ключом сразу удалится из чата.\n\n"
                                              f"Адрес API: <code>{esc(url)}</code> — если у сайта другой, поменяете "
                                              f"потом в «Сайты-поставщики».", "qa_key", {}, self.cb("go1"))
            return
        self.ask(call, call.from_user.id, "Пришлите <b>адрес API</b> панели — он есть на странице «API» сайта, "
                                          "обычно вида <code>https://сайт.com/api/v2</code>:", "qa_url", {},
                 self.cb("go1"))

    def i_qa_url(self, target: tuple, uid: int, text: str, data: dict) -> None:
        url = text.strip().rstrip("/")
        if not re.match(r"^https?://\S+\.\S+", url):
            self.ask(target, uid, "❗ Это не похоже на адрес. Пример: <code>https://site.com/api/v2</code>. "
                                  "Попробуйте ещё раз:", "qa_url", {}, self.cb("go1"))
            return None
        if not re.search(r"/api", url):
            url += "/api/v2"
        self.sess(uid).setdefault("qa", {})["url"] = url
        self.ask(target, uid, f"Адрес: <code>{esc(url)}</code>\nТеперь пришлите <b>API-ключ</b> (сообщение удалится):",
                 "qa_key", {}, self.cb("go1"))
        return None

    def i_qa_key(self, target: tuple, uid: int, text: str, data: dict) -> None:
        qa = self.sess(uid).get("qa") or {"preset": "smmway"}
        qa["key"] = text.strip()

        def work() -> tuple:
            preset = qa["preset"]
            profile = json.loads(json.dumps(PRESETS[preset]["profile"]))
            if qa.get("url"):
                profile["base_url"] = qa["url"]
                host = re.sub(r"^https?://(www\.)?", "", qa["url"]).split("/")[0]
                profile["name"] = host
            s = SupplierBase.create_from_profile(profile, qa["key"], 0, lambda: True)
            try:
                bal, cur = s.get_balance()
                if cur in ("USD", "RUB", "EUR"):
                    profile["currency"] = cur
            except SupplierError as e:
                kb = K().row(B("🔑 Ввести ключ ещё раз", callback_data=self.cb("qa", preset)))
                kb.row(B("🛠 Ручная настройка", callback_data=self.cb("sa")))
                hint = "Ключ не подошёл." if e.code == "auth" else f"Сайт ответил ошибкой: {esc(e.message)}."
                raw = f"\n<code>{esc(s.last_raw[:300])}</code>" if s.last_raw else ""
                return f"❌ {hint}{raw}\nПроверьте ключ и адрес API.", self.nav(kb, self.cb("go"))
            existing = [r for r in self.p.sup.list() if r["preset"] == preset and r["needs_key"]]
            if existing:
                sid = existing[0]["id"]
                self.p.sup.update_profile(sid, dict(self.p.sup.profile(sid), currency=profile["currency"],
                                                    base_url=profile["base_url"]))
                self.p.sup.set_key(sid, qa["key"])
                self.p.sup.set_field(sid, "enabled", 1)
            else:
                sid = self.p.sup.add(profile, qa["key"], enabled=True)
            try:
                n = self.p.sup.refresh_catalog(sid, force=True)
            except SupplierError as e:
                n = 0
                log_warn(f"Каталог: {e.message}")
            self.sess(uid).pop("qa", None)
            text_, kb = self.r_go(None)
            return (f"✅ <b>Сайт подключён!</b> Баланс: {money(bal)} {esc(cur)}, услуг: {n}.\n\n" + text_), kb

        self.bg(target, work, "⏳ Проверяю подключение…")
        return None

    def r_go2(self, call: CallbackQuery, *args: str) -> tuple:
        cur = self.p.cfg.get("margin_default")
        kb = K()
        row = []
        for m in (15, 20, 25, 30, 40, 50):
            row.append(B(("✅" if float(cur) == m else "") + f"{m}%", callback_data=self.cb("go2s", m)))
            if len(row) == 3:
                kb.row(*row)
                row = []
        kb.row(B("✏️ Своя", callback_data=self.cb("go2c")))
        example = Decimal("100") * (1 + D(cur) / 100)
        return ("<b>Шаг 2. Наценка</b>\nСколько вы зарабатываете сверх цены сайта.\n"
                f"Сейчас: <b>{cur}%</b> — услуга за 100 ₽ продаётся примерно за {money(example)} ₽ "
                f"(+ комиссии, если заданы).\n\n💡 Новичкам: 25-30%. Цены лотов пересчитываются сами, если сайт "
                f"поменяет свою цену."), self.nav(kb, self.cb("go"))

    def r_go2s(self, call: CallbackQuery, value: str) -> tuple:
        self.p.cfg.set("margin_default", float(value))
        self.p.db.meta_set("setup_margin", 1)
        text, kb = self.r_go(call)
        return f"✅ Наценка {value}% сохранена.\n\n" + text, kb

    def r_go2c(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Наценка в % (например 27):", "go2c", {}, self.cb("go2"))

    def i_go2c(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        value = float(Config.coerce("pct", text))
        return self.r_go2s(None, str(value))

    def r_go3(self, call: CallbackQuery, *args: str) -> tuple:
        if not any(not s["needs_key"] for s in self.p.sup.list(enabled_only=True)):
            return "Сначала подключите сайт (шаг 1).", self.nav(K().row(B("1. Подключить сайт",
                                                                          callback_data=self.cb("go1"))), self.cb("go"))
        return self.r_nl(call)

    def r_go4(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        if self.p.dry:
            kb.row(B("✅ Включить боевой режим", callback_data=self.cb("go4s", 0)))
        else:
            kb.row(B("🧪 Вернуть тестовый режим", callback_data=self.cb("go4s", 1)))
        return ("<b>Шаг 4. Боевой режим</b>\n"
                f"Сейчас: <b>{'🧪 тестовый' if self.p.dry else '✅ боевой'}</b>.\n\n"
                "🧪 В тестовом режиме плагин всё делает «понарошку»: лоты не выставляются, заказы поставщику не "
                "уходят, покупателям ничего не пишется — только записи в лог.\n"
                "✅ В боевом режиме всё работает по-настоящему. Перед включением пополните баланс сайта."), \
            self.nav(kb, self.cb("go"))

    def r_go4s(self, call: CallbackQuery, dry: str) -> tuple:
        self.p.cfg.set("dry_run", bool(int(dry)))
        text, kb = self.r_go(call)
        return ("🧪 Тестовый режим включён.\n\n" if int(dry) else "✅ Боевой режим включён!\n\n") + text, kb

    def r_m(self, call: CallbackQuery, *args: str) -> tuple:
        self.tg.clear_state(call.message.chat.id, call.from_user.id)
        return self.scr_main(call.from_user.id)

    def supplier_buttons(self, kb: K, action: str, *extra: Any) -> None:
        sups = self.p.sup.list(enabled_only=True)
        for s in sups:
            kb.row(B(f"🔌 {s['name']}", callback_data=self.cb(action, *extra, s["id"])))
        if not sups:
            kb.row(B("➕ Добавить поставщика", callback_data=self.cb("sa")))

    # ── каталог ──
    def r_cat(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        self.supplier_buttons(kb, "cs")
        return "<b>📦 Каталог</b>\nВыберите поставщика:", self.nav(kb, self.cb("m"))

    def r_cs(self, call: CallbackQuery, sid: str, page: str = "0") -> Optional[tuple]:
        sid_i = int(sid)
        if self.p.sup.catalog_age(sid_i) is None:
            def work() -> tuple:
                self.p.sup.refresh_catalog(sid_i, force=True)
                return self.scr_cs(sid_i, 0)
            self.bg(call, work, "⏳ Загружаю каталог…")
            return None
        return self.scr_cs(sid_i, int(page))

    def scr_cs(self, sid: int, page: int) -> tuple[str, K]:
        row = self.p.sup.row(sid)
        cats = self.p.sup.categories(sid)
        kb = K()
        kb.row(B("🔄 Обновить каталог", callback_data=self.cb("cref", sid)),
               B("🔍 Поиск", callback_data=self.cb("csrch", sid)))
        self.paginate(kb, list(enumerate(cats)), page,
                      lambda it: B(it[1][:60], callback_data=self.cb("cc", sid, it[0], 0)),
                      lambda pg: self.cb("cs", sid, pg))
        age = self.p.sup.catalog_age(sid)
        text = (f"<b>📦 {esc(row['name'] if row else sid)}</b>\nКатегорий: {len(cats)}, " +
                (f"обновлено {fmt_duration(age)} назад" if age is not None else "каталог пуст"))
        return text, self.nav(kb, self.cb("cat"))

    def r_cref(self, call: CallbackQuery, sid: str) -> None:
        def work() -> tuple:
            n = self.p.sup.refresh_catalog(int(sid), force=True)
            text, kb = self.scr_cs(int(sid), 0)
            return f"✅ Обновлено, услуг: {n}\n\n" + text, kb
        self.bg(call, work, "⏳ Обновляю каталог…")

    def r_csrch(self, call: CallbackQuery, sid: str) -> None:
        self.ask(call, call.from_user.id, "Введите текст для поиска по названию или ID услуги:", "csearch",
                 {"sid": int(sid)}, self.cb("cs", sid, 0))

    def i_csearch(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        self.sess(uid)["search"] = text
        return self.scr_search(uid, data["sid"], 0)

    def r_csr(self, call: CallbackQuery, sid: str, page: str) -> tuple:
        return self.scr_search(call.from_user.id, int(sid), int(page))

    def scr_search(self, uid: int, sid: int, page: int) -> tuple:
        q = self.sess(uid).get("search", "")
        items = self.p.sup.services(sid, text=q)
        kb = K()
        self.paginate(kb, items, page, lambda s: self.service_btn(sid, s), lambda pg: self.cb("csr", sid, pg))
        return f"🔍 «{esc(q)}»: найдено {len(items)}", self.nav(kb, self.cb("cs", sid, 0))

    def service_btn(self, sid: int, s: dict) -> B:
        try:
            p1k = money(self.p.price.calc_service(sid, s, 1000)["price"])
        except Exception:
            p1k = "?"
        mark = "⛔" if s["disabled"] else ""
        return B(f"{mark}{s['service_id']} | {s['name'][:38]} | {p1k}₽/1k",
                 callback_data=self.cb("sv", sid, s["service_id"]))

    def r_cc(self, call: CallbackQuery, sid: str, idx: str, page: str = "0") -> tuple:
        sid_i = int(sid)
        cats = self.p.sup.categories(sid_i)
        if int(idx) >= len(cats):
            return self.scr_cs(sid_i, 0)
        cat = cats[int(idx)]
        items = self.p.sup.services(sid_i, category=cat)
        kb = K()
        self.paginate(kb, items, int(page), lambda s: self.service_btn(sid_i, s),
                      lambda pg: self.cb("cc", sid, idx, pg))
        cm = (self.p.cfg.get("margins.category") or {}).get(cat)
        kb.row(B(f"📈 Маржа категории ({cm if cm is not None else 'по умолч.'}%)",
                 callback_data=self.cb("ccm", sid, idx)))
        return f"<b>{esc(cat)}</b>\nУслуг: {len(items)}", self.nav(kb, self.cb("cs", sid, 0))

    def r_ccm(self, call: CallbackQuery, sid: str, idx: str) -> None:
        self.ask(call, call.from_user.id, "Маржа категории в % (или «-» — сбросить):", "ccm",
                 {"sid": int(sid), "idx": int(idx)}, self.cb("cc", sid, idx, 0))

    def i_ccm(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        cats = self.p.sup.categories(data["sid"])
        cat = cats[data["idx"]]
        margins = dict(self.p.cfg.get("margins.category") or {})
        if text == "-":
            margins.pop(cat, None)
        else:
            margins[cat] = float(Config.coerce("pct", text))
        self.p.cfg.set("margins.category", margins)
        return self.r_cc(None, str(data["sid"]), str(data["idx"]), "0")

    def scr_service(self, sid: int, svc: str) -> tuple[str, K]:
        s = self.p.sup.service(sid, svc)
        if not s:
            return "Услуга не найдена (обновите каталог).", self.nav(K(), self.cb("cs", sid, 0))
        sup = self.p.sup.get(sid)
        calc = self.p.price.calc_service(sid, s, 1000)
        rating, total = self.p.cat.rating(sid, svc)
        lots = self.p.db.query("SELECT l.id, l.title, l.fp_lot_id FROM lot_services ls JOIN lots l ON l.id=ls.lot_id "
                               "WHERE ls.supplier_id=? AND ls.service_id=?", (sid, str(svc)))
        cats = self.p.sup.categories(sid)
        idx = cats.index(s["category"]) if s["category"] in cats else 0
        bound = ", ".join("#" + str(x["id"]) for x in lots)
        text = (f"<b>{esc(s['name'])}</b>\nID: <code>{esc(s['service_id'])}</code> | {esc(sup.name if sup else sid)}\n"
                f"Категория: {esc(s['category'])}\n"
                f"Ставка: {esc(s['rate'])} {esc(sup.currency if sup else '')} за {sup.rate_unit if sup else 1000}\n"
                f"Мин/макс: {s['min']} / {s['max']} | Refill: {_yes_no(s['refill'])} | Cancel: {_yes_no(s['cancel'])}\n"
                f"\nЗа 1000 шт.: себестоимость <b>{money(calc['cost'])} ₽</b>, цена <b>{money(calc['price'])} ₽</b>, "
                f"чистая прибыль <b>{money(calc['profit'])} ₽</b>\nМаржа: {calc['margin']}% ({esc(calc['margin_src'])})\n"
                f"Рейтинг: {rating:.2f} (заказов {total})\n"
                f"Состояние: {'⛔ отключена' if s['disabled'] else '✅ активна'}\n"
                f"Привязанные лоты: {bound or 'нет'}")
        kb = K()
        kb.row(B("📈 Маржа услуги", callback_data=self.cb("svm", sid, svc)),
               B("🔗 Привязать к лоту", callback_data=self.cb("svb", sid, svc, 0)))
        kb.row(B("🆔 Привязать лот FP по ID", callback_data=self.cb("svf", sid, svc)),
               B("▶️ Включить" if s["disabled"] else "⛔ Отключить", callback_data=self.cb("svd", sid, svc)))
        return text, self.nav(kb, self.cb("cc", sid, idx, 0))

    def r_sv(self, call: CallbackQuery, sid: str, svc: str) -> tuple:
        return self.scr_service(int(sid), svc)

    def r_svd(self, call: CallbackQuery, sid: str, svc: str) -> tuple:
        s = self.p.sup.service(int(sid), svc)
        self.p.db.execute("UPDATE services SET disabled=? WHERE supplier_id=? AND service_id=?",
                          (0 if s["disabled"] else 1, int(sid), svc))
        return self.scr_service(int(sid), svc)

    def r_svm(self, call: CallbackQuery, sid: str, svc: str) -> None:
        self.ask(call, call.from_user.id, "Маржа услуги в % (или «-» — сбросить):", "svm",
                 {"sid": int(sid), "svc": svc}, self.cb("sv", sid, svc))

    def i_svm(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        margins = dict(self.p.cfg.get("margins.service") or {})
        key = f"{data['sid']}:{data['svc']}"
        if text == "-":
            margins.pop(key, None)
        else:
            margins[key] = float(Config.coerce("pct", text))
        self.p.cfg.set("margins.service", margins)
        return self.scr_service(data["sid"], data["svc"])

    def r_svb(self, call: CallbackQuery, sid: str, svc: str, page: str = "0") -> tuple:
        lots = self.p.db.query("SELECT * FROM lots WHERE lost=0 ORDER BY id DESC")
        kb = K()
        self.paginate(kb, lots, int(page),
                      lambda l: B(f"#{l['id']} {(l['title'] or '')[:45]}", callback_data=self.cb("svbl", sid, svc,
                                                                                               l["id"])),
                      lambda pg: self.cb("svb", sid, svc, pg))
        return "Выберите лот плагина, к которому добавить услугу кандидатом:", self.nav(kb, self.cb("sv", sid, svc))

    def r_svbl(self, call: CallbackQuery, sid: str, svc: str, lid: str) -> tuple:
        self.p.ml._ensure_candidate(int(lid), int(sid), svc)
        self.toast(call, "Услуга добавлена кандидатом")
        return self.scr_lot(int(lid))

    def r_svf(self, call: CallbackQuery, sid: str, svc: str) -> None:
        self.ask(call, call.from_user.id, "Введите ID существующего лота FunPay (число из ссылки offer?id=…):", "svf",
                 {"sid": int(sid), "svc": svc}, self.cb("sv", sid, svc))

    def i_svf(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        fp_id = int(re.findall(r"\d+", text)[-1])
        lid = self.p.ml.bind_fp_lot(fp_id, data["sid"], data["svc"])
        return self.scr_lot(lid)

    # ── мастер-лоты ──
    def r_tg(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        for key, preset in TEMPLATE_PRESETS.items():
            kb.row(B(preset["title"], callback_data=self.cb("tgp", key)))
        return ("<b>🪄 Галерея шаблонов</b>\nГотовые продающие заголовки и описания с кодовыми словами. "
                "После выбора останется указать категорию FunPay — остальное можно поправить позже."), \
            self.nav(kb, self.cb("ml"))

    def r_tgp(self, call: CallbackQuery, key: str) -> Optional[tuple]:
        preset = TEMPLATE_PRESETS[key]
        tpl = {k: preset[k] for k in MasterLot.TEMPLATE_FIELDS if k in preset}
        self.sess(call.from_user.id)["tpl"] = tpl
        self.sess(call.from_user.id)["tpl_fast"] = True
        self.sess(call.from_user.id)["tpl_keywords"] = preset.get("keywords") or []
        self.sess(call.from_user.id)["tpl_hints"] = preset.get("node_hints") or []
        step = [k for k, _p, _r in TEMPLATE_STEPS].index("category_node")
        return self.tpl_step(call, call.from_user.id, step)

    def example_text(self, text: str) -> str:
        """Живой пример подстановки кодовых слов на реальной услуге из каталога."""
        if not text:
            return ""
        sample = self.p.db.one("SELECT * FROM services WHERE disabled=0 ORDER BY refill DESC LIMIT 1")
        if not sample:
            return ""
        sup = self.p.sup.row(sample["supplier_id"]) or {"id": sample["supplier_id"], "name": "?"}
        try:
            p1k = self.p.price.calc_service(sample["supplier_id"], sample, 1000)["price"]
        except Exception:
            p1k = Decimal("0")
        ctx = {"p": self.p, "svc": sample, "supplier": sup, "template": {}, "unit": 1000, "price_per_1k": p1k,
               "marker": MasterLot.marker(sample["supplier_id"], sample["service_id"])}
        rendered, unknown = render_codewords(text, LOT_CODE_RESOLVERS, ctx)
        res = esc(re.sub(r"[ \t]+", " ", rendered).strip()[:300])
        if unknown:
            res += "\n⚠️ Неизвестные слова: " + ", ".join("{" + esc(u) + "}" for u in sorted(unknown))
        return res

    def node_search(self, query: str, hints: Optional[list] = None) -> list:
        """Поиск подкатегорий FunPay по тексту (с синонимами: «тикток» = «tiktok»); hints поднимают нужные выше."""
        words = [w for w in norm_text(query).split() if w]
        variants = [SEARCH_SYNONYMS.get(w, [w]) for w in words]
        result = []
        try:
            subs = self.c.account.subcategories
        except Exception:
            subs = []
        for sub in subs:
            if sub.type is not SubCategoryTypes.COMMON:
                continue
            name = f" {norm_text(sub.fullname)} "
            if all(any(v in name for v in group) for group in variants):
                result.append(sub)
        hints = [norm_text(h) for h in (hints or [])]

        def rank(s: Any) -> tuple:
            name = norm_text(s.fullname)
            hit = next((i for i, h in enumerate(hints) if h in name), len(hints))
            return hit, len(s.fullname), s.fullname

        result.sort(key=rank)
        return result[:PAGE_SIZE * 2]

    def node_buttons(self, uid: int, subs: list, action: str, *extra: Any) -> K:
        self.sess(uid)["node_results"] = [(s.id, s.fullname) for s in subs]
        kb = K()
        for i, s in enumerate(subs):
            kb.row(B(f"{s.name} — {s.category.name}"[:60], callback_data=self.cb(action, *extra, i)))
        return kb

    def r_cw(self, call: CallbackQuery, *args: str) -> tuple:
        sample = self.p.db.one("SELECT * FROM services WHERE disabled=0 LIMIT 1")
        lines = ["<b>🔤 Кодовые слова лотов</b>"]
        ctx = None
        if sample:
            sup = self.p.sup.row(sample["supplier_id"]) or {"id": sample["supplier_id"], "name": "?"}
            try:
                p1k = self.p.price.calc_service(sample["supplier_id"], sample, 1000)["price"]
            except Exception:
                p1k = Decimal("0")
            ctx = {"p": self.p, "svc": sample, "supplier": sup, "template": {}, "unit": 1000, "price_per_1k": p1k,
                   "marker": MasterLot.marker(sample["supplier_id"], sample["service_id"])}
        for k, v in LOT_CODE_WORDS_HELP.items():
            ex = ""
            if ctx:
                try:
                    ex = f" → <i>{esc(LOT_CODE_RESOLVERS[k](ctx))[:60]}</i>"
                except Exception:
                    ex = ""
            lines.append(f"<code>{{{k}}}</code> — {esc(v)}{ex}")
        lines.append("\n<b>Кодовые слова сообщений</b>")
        for k, v in MESSAGE_CODE_WORDS_HELP.items():
            lines.append(f"<code>{{{k}}}</code> — {esc(v)}")
        lines.append("\nНеизвестные слова остаются как есть и попадают в отчёт.")
        return "\n".join(lines), self.nav(K(), self.cb("ml"))

    def r_sync(self, call: CallbackQuery, *args: str) -> None:
        self.bg(call, lambda: (self.p.sync.run(), self.nav(K(), self.cb("ml"))), "⏳ Синхронизация с FunPay…")

    def r_tn(self, call: CallbackQuery, *args: str) -> None:
        self.sess(call.from_user.id)["tpl"] = {}
        self.tpl_step(call, call.from_user.id, 0)

    def tpl_step(self, target: Any, uid: int, step: int, notice: str = "") -> Optional[tuple]:
        sess = self.sess(uid)
        data = sess.setdefault("tpl", {})
        fast = sess.get("tpl_fast")
        while step < len(TEMPLATE_STEPS):
            key = TEMPLATE_STEPS[step][0]
            if key == "quantity_pack" and data.get("price_mode") != "pack":
                step += 1
                continue
            if fast and key != "category_node" and key in data:
                step += 1
                continue
            break
        if step >= len(TEMPLATE_STEPS):
            tid = self.p.ml.save_template(data)
            for k in ("tpl", "tpl_fast", "tpl_keywords", "tpl_hints"):
                sess.pop(k, None)
            return self.scr_template(tid, "✅ Шаблон сохранён. Нажмите «🚀 Запуск», чтобы выставить лоты.")
        key, prompt, required = TEMPLATE_STEPS[step]
        header = (notice + "\n\n" if notice else "") + f"<b>Новый шаблон — шаг {step + 1}/{len(TEMPLATE_STEPS)}</b>\n"
        tip = TEMPLATE_STEP_TIPS.get(key, "")
        prev = {"title_en": "title_ru", "desc_ru": "title_ru", "desc_en": "desc_ru", "category_node": "desc_ru"}.get(key)
        example = self.example_text(data.get(prev, "")) if prev and data.get(prev) else ""
        body = prompt + (f"\n\n{tip}" if tip else "")
        if example:
            body += f"\n\n👁 Так будет выглядеть «{TEMPLATE_FIELD_TITLES.get(prev, prev)}»:\n<i>{example}</i>"
        if key == "price_mode":
            kb = K()
            for m, title in PRICE_MODE_TITLES.items():
                kb.row(B(title, callback_data=self.cb("tpm", m, step)))
            kb.row(B("❌ Отмена", callback_data=self.cb("ml")))
            self.show(target, header + body, kb)
            return None
        if key == "category_node" and sess.get("tpl_keywords"):
            subs = self.node_search(sess["tpl_keywords"][0], sess.get("tpl_hints"))
            if subs:
                kb = self.node_buttons(uid, subs, "tnode", step)
                kb.row(B("❌ Отмена", callback_data=self.cb("ml")))
                self.show(target, header + body + "\n\nПодходящие категории (или введите свой запрос/ID):", kb)
                self.tg.set_state(*self._target_ids(target), uid, STATE_INPUT,
                                  {"kind": "tpl_step", "step": step, "back": self.cb("ml")})
                return None
        self.ask(target, uid, header + body, "tpl_step", {"step": step}, self.cb("ml"))
        return None

    @staticmethod
    def _target_ids(target: Any) -> tuple[int, int]:
        if isinstance(target, CallbackQuery):
            return target.message.chat.id, target.message.id
        return target[0], target[1]

    def r_tnode(self, call: CallbackQuery, step: str, idx: str) -> Optional[tuple]:
        res = self.sess(call.from_user.id).get("node_results") or []
        if int(idx) >= len(res):
            return None
        self.tg.clear_state(call.message.chat.id, call.from_user.id)
        node_id, name = res[int(idx)]
        self.sess(call.from_user.id).setdefault("tpl", {})["category_node"] = int(node_id)
        return self.tpl_step(call, call.from_user.id, int(step) + 1, f"✅ Категория: {esc(name)} (node {node_id})")

    def r_tpm(self, call: CallbackQuery, mode: str, step: str) -> None:
        self.sess(call.from_user.id).setdefault("tpl", {})["price_mode"] = mode
        res = self.tpl_step(call, call.from_user.id, int(step) + 1)
        if isinstance(res, tuple):
            self.show(call, *res)

    def i_tpl_step(self, target: tuple, uid: int, text: str, data: dict) -> Optional[tuple]:
        step = int(data["step"])
        key, _prompt, required = TEMPLATE_STEPS[step]
        tpl = self.sess(uid).setdefault("tpl", {})
        value: Any = "" if (text == "-" and not required) else text
        if key == "category_node":
            nums = re.findall(r"\d+", text)
            if not nums or re.search(r"[a-zA-Zа-яА-ЯёЁ]{3,}", text) and "funpay" not in text.lower():
                subs = self.node_search(text)
                if not subs:
                    self.ask(target, uid, f"🔍 По запросу «{esc(text)}» ничего не найдено. Введите другое название "
                                          f"(например «instagram», «tiktok») или ID числом:", "tpl_step", data,
                             self.cb("ml"))
                    return None
                kb = self.node_buttons(uid, subs, "tnode", step)
                kb.row(B("❌ Отмена", callback_data=self.cb("ml")))
                self.show(target, f"🔍 Найдено по «{esc(text)}» — выберите категорию (или введите другой запрос):", kb)
                self.tg.set_state(target[0], target[1], uid, STATE_INPUT,
                                  {"kind": "tpl_step", "step": step, "back": self.cb("ml")})
                return None
            value = int(nums[-1])
            sub = self.c.account.get_subcategory(SubCategoryTypes.COMMON, value)
            if sub:
                tpl[key] = value
                return self.tpl_step(target, uid, step + 1, f"✅ Категория: {esc(sub.fullname)} (node {value})")
        if key == "quantity_pack" and not re.findall(r"\d+", text):
            self.ask(target, uid, "❗ Укажите хотя бы один пакет, например 100, 500, 1000:", "tpl_step", data,
                     self.cb("ml"))
            return None
        if required and value in ("", "-"):
            self.ask(target, uid, "❗ Поле обязательно. Введите значение:", "tpl_step", data, self.cb("ml"))
            return None
        tpl[key] = value
        return self.tpl_step(target, uid, step + 1)

    def scr_template(self, tid: int, notice: str = "") -> tuple[str, K]:
        t = self.p.ml.template(tid)
        if not t:
            return "Шаблон не найден.", self.nav(K(), self.cb("ml"))
        cnt = self.p.db.scalar("SELECT COUNT(*) FROM lots WHERE template_id=?", (tid,), 0)
        text = (f"{notice + chr(10) if notice else ''}<b>🏷 {esc(t['name'])}</b> (#{tid})\n"
                f"Заголовок RU: {esc((t['title_ru'] or '')[:150])}\n"
                f"Заголовок EN: {esc((t['title_en'] or '—')[:150])}\n"
                f"Описание RU: {esc((t['desc_ru'] or '')[:300])}\n"
                f"Категория (node): {t['category_node']}\n"
                f"Режим цены: {esc(PRICE_MODE_TITLES.get(t['price_mode'], t['price_mode']))}"
                f"{' — пакеты ' + esc(t['quantity_pack']) if t['price_mode'] == 'pack' else ''}\n"
                f"Автовыдача: {'есть' if t['secrets_text'] else 'нет'} | Автоответ: "
                f"{'есть' if t['autoreply_text'] else 'нет'}\nЛотов по шаблону: {cnt}")
        kb = K()
        kb.row(B("🚀 Запуск", callback_data=self.cb("tr", tid)), B("✏️ Изменить", callback_data=self.cb("te", tid)))
        kb.row(B("🗑 Удалить", callback_data=self.cb("td", tid)))
        return text, self.nav(kb, self.cb("ml"))

    def r_t(self, call: CallbackQuery, tid: str) -> tuple:
        return self.scr_template(int(tid))

    def r_te(self, call: CallbackQuery, tid: str) -> tuple:
        kb = K()
        for key, _p, _r in TEMPLATE_STEPS:
            kb.row(B(TEMPLATE_FIELD_TITLES[key][:50], callback_data=self.cb("tef", tid, key)))
        return "Какое поле изменить?", self.nav(kb, self.cb("t", tid))

    def r_tef(self, call: CallbackQuery, tid: str, key: str) -> Optional[tuple]:
        t = self.p.ml.template(int(tid))
        if key == "price_mode":
            kb = K()
            for m, title in PRICE_MODE_TITLES.items():
                kb.row(B(("✅ " if t["price_mode"] == m else "") + title, callback_data=self.cb("tefm", tid, m)))
            return "Режим цены:", self.nav(kb, self.cb("te", tid))
        prompt = dict((k, p) for k, p, _r in TEMPLATE_STEPS)[key]
        self.ask(call, call.from_user.id, f"{prompt}\n\nТекущее значение:\n<code>{esc(t[key] or '—')[:1500]}</code>",
                 "tpl_edit", {"tid": int(tid), "key": key}, self.cb("t", tid))
        return None

    def r_tefm(self, call: CallbackQuery, tid: str, mode: str) -> tuple:
        self.p.ml.save_template({"price_mode": mode}, int(tid))
        return self.scr_template(int(tid), "✅ Сохранено.")

    def i_tpl_edit(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        key = data["key"]
        value: Any = "" if text == "-" else text
        if key == "category_node":
            nums = re.findall(r"\d+", text)
            if not nums:
                subs = self.node_search(text)
                if not subs:
                    return f"🔍 По «{esc(text)}» ничего не найдено.", self.nav(K(), self.cb("te", data["tid"]))
                kb = self.node_buttons(uid, subs, "tenode", data["tid"])
                return "Выберите категорию для шаблона:", self.nav(kb, self.cb("te", data["tid"]))
            value = int(nums[-1])
        self.p.ml.save_template({key: value}, data["tid"])
        return self.scr_template(data["tid"], "✅ Сохранено.")

    def r_tenode(self, call: CallbackQuery, tid: str, idx: str) -> tuple:
        res = self.sess(call.from_user.id).get("node_results") or []
        node_id, name = res[int(idx)]
        self.p.ml.save_template({"category_node": int(node_id)}, int(tid))
        return self.scr_template(int(tid), f"✅ Категория: {esc(name)}")

    def r_td(self, call: CallbackQuery, tid: str) -> tuple:
        kb = K().row(B("🗑 Да, удалить", callback_data=self.cb("tdy", tid)),
                     B("Отмена", callback_data=self.cb("t", tid)))
        return "Удалить шаблон? Лоты останутся на FunPay и в базе (без шаблона).", kb

    def r_tdy(self, call: CallbackQuery, tid: str) -> tuple:
        self.p.ml.delete_template(int(tid))
        return self.r_ml(call)

    # ── запуск мастер-лота ──
    def r_tr(self, call: CallbackQuery, tid: str) -> tuple:
        kb = K()
        self.supplier_buttons(kb, "trs", tid)
        return "Выберите поставщика для генерации лотов:", self.nav(kb, self.cb("t", tid))

    def r_trs(self, call: CallbackQuery, tid: str, sid: str) -> Optional[tuple]:
        if self.p.sup.catalog_age(int(sid)) is None:
            def work() -> tuple:
                self.p.sup.refresh_catalog(int(sid), force=True)
                return self.r_trs(call, tid, sid)
            self.bg(call, work, "⏳ Загружаю каталог…")
            return None
        kb = K()
        kb.row(B("⭐ Авто-подбор лучших услуг", callback_data=self.cb("trm", tid, sid, "rec", 0)))
        kb.row(B("📂 Вся категория", callback_data=self.cb("trm", tid, sid, "cat", 0)))
        kb.row(B("☑️ Выбранные услуги", callback_data=self.cb("trm", tid, sid, "sel", 0)))
        kb.row(B("🔎 По фильтру", callback_data=self.cb("trf", tid, sid)))
        self.sess(call.from_user.id)["sel"] = set()
        return ("Режим запуска:\n⭐ <b>Авто-подбор</b> — плагин сам выберет в категории до 5 лучших услуг: самую "
                "дешёвую, самую дешёвую с гарантией, самую надёжную по статистике и т.д.\n"
                "📂 Вся категория — лот на каждую услугу категории.\n☑️ Выбранные — отметить вручную.\n"
                "🔎 Фильтр — по тексту и цене."), self.nav(kb, self.cb("tr", tid))

    def r_trm(self, call: CallbackQuery, tid: str, sid: str, mode: str, page: str = "0") -> tuple:
        cats = self.p.sup.categories(int(sid))
        kb = K()
        act = {"cat": "trc", "rec": "trrec"}.get(mode, "trsc")
        t = self.p.ml.template(int(tid)) or {}
        plat = detect_platform(t.get("name"), t.get("title_ru"), t.get("desc_ru"))
        items = list(enumerate(cats))
        if plat:
            keys = [k.strip() for k in next(p[1] for p in PLATFORMS if p[0] == plat[0])]
            items.sort(key=lambda it: 0 if any(k in norm_text(it[1]) for k in keys) else 1)
            match = lambda name: any(k in norm_text(name) for k in keys)  # noqa: E731
        else:
            match = lambda name: False  # noqa: E731
        self.paginate(kb, items, int(page),
                      lambda it: B(("🎯 " if match(it[1]) else "") + it[1][:58],
                                   callback_data=self.cb(act, tid, sid, it[0], 0)),
                      lambda pg: self.cb("trm", tid, sid, mode, pg))
        if mode == "sel":
            n = len(self.sess(call.from_user.id).get("sel", set()))
            kb.row(B(f"👁 Предпросмотр ({n})", callback_data=self.cb("trp", tid, sid)))
        hint = f"\n🎯 — категории под платформу шаблона ({plat[0]})." if plat else ""
        return "Выберите категорию услуг поставщика:" + hint, self.nav(kb, self.cb("trs", tid, sid))

    def r_trrec(self, call: CallbackQuery, tid: str, sid: str, idx: str, page: str = "0") -> tuple:
        cats = self.p.sup.categories(int(sid))
        picks = self.p.ml.recommend(int(sid), cats[int(idx)], int(tid))
        if not picks:
            self.toast(call, "В категории нет подходящих услуг", True)
            return self.r_trm(call, tid, sid, "rec", "0")
        self.sess(call.from_user.id)["run"] = {"tid": int(tid), "sid": int(sid), "mode": "sel",
                                               "arg": [p["service_id"] for p in picks],
                                               "why": {p["service_id"]: p["why"] for p in picks}}
        return self.scr_run_preview(call.from_user.id)

    def r_trc(self, call: CallbackQuery, tid: str, sid: str, idx: str, page: str = "0") -> tuple:
        cats = self.p.sup.categories(int(sid))
        self.sess(call.from_user.id)["run"] = {"tid": int(tid), "sid": int(sid), "mode": "cat",
                                               "arg": cats[int(idx)]}
        return self.scr_run_preview(call.from_user.id)

    def r_trsc(self, call: CallbackQuery, tid: str, sid: str, idx: str, page: str = "0") -> tuple:
        cats = self.p.sup.categories(int(sid))
        items = self.p.sup.services(int(sid), category=cats[int(idx)], include_disabled=False)
        sel: set = self.sess(call.from_user.id).setdefault("sel", set())
        kb = K()
        self.paginate(kb, items, int(page),
                      lambda s: B(f"{'✅' if s['service_id'] in sel else '⬜'} {s['service_id']} {s['name'][:40]}",
                                  callback_data=self.cb("trt", tid, sid, idx, page, s["service_id"])),
                      lambda pg: self.cb("trsc", tid, sid, idx, pg))
        kb.row(B(f"👁 Предпросмотр ({len(sel)})", callback_data=self.cb("trp", tid, sid)))
        return f"Отметьте услуги ({esc(cats[int(idx)])}):", self.nav(kb, self.cb("trm", tid, sid, "sel", 0))

    def r_trt(self, call: CallbackQuery, tid: str, sid: str, idx: str, page: str, svc: str) -> tuple:
        sel: set = self.sess(call.from_user.id).setdefault("sel", set())
        sel.symmetric_difference_update({svc})
        return self.r_trsc(call, tid, sid, idx, page)

    def r_trp(self, call: CallbackQuery, tid: str, sid: str) -> tuple:
        sel = sorted(self.sess(call.from_user.id).get("sel", set()))
        if not sel:
            self.toast(call, "Не выбрано ни одной услуги", True)
            return self.r_trm(call, tid, sid, "sel", "0")
        self.sess(call.from_user.id)["run"] = {"tid": int(tid), "sid": int(sid), "mode": "sel", "arg": sel}
        return self.scr_run_preview(call.from_user.id)

    def r_trf(self, call: CallbackQuery, tid: str, sid: str) -> None:
        self.ask(call, call.from_user.id, "Фильтр: <code>текст;мин_цена;макс_цена</code> (цена за 1000 в ₽).\n"
                                          "Например: <code>followers;50;300</code> или <code>likes;;</code>",
                 "run_filter", {"tid": int(tid), "sid": int(sid)}, self.cb("trs", tid, sid))

    def i_run_filter(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        parts = (text.split(";") + ["", "", ""])[:3]
        lo = parts[1].strip() or None
        hi = parts[2].strip() or None
        self.sess(uid)["run"] = {"tid": data["tid"], "sid": data["sid"], "mode": "flt",
                                 "arg": (parts[0].strip(), lo, hi)}
        return self.scr_run_preview(uid)

    def scr_run_preview(self, uid: int) -> tuple:
        run = self.sess(uid).get("run")
        services = self.p.ml.select_services(run["sid"], run["mode"], run["arg"])
        run["services"] = [s["service_id"] for s in services]
        margin = D(run["margin"]) if run.get("margin") is not None else None
        text = self.p.ml.preview(run["tid"], run["sid"], services, margin=margin)
        if run.get("why"):
            text += "\n\n<b>⭐ Почему выбраны:</b>\n" + "\n".join(
                f"• {esc(k)}: {esc(v)}" for k, v in run["why"].items())
        presets = self.p.cfg.get("masterlot.margin_presets") or [15, 20, 25, 30, 40, 50]
        kb = K()
        row = []
        for m in presets:
            mark = "✅" if margin is not None and D(m) == margin else ""
            row.append(B(f"{mark}{m}%", callback_data=self.cb("trmg", m)))
            if len(row) == 3:
                kb.row(*row)
                row = []
        if row:
            kb.row(*row)
        kb.row(B("✏️ Своя наценка", callback_data=self.cb("trmgc")),
               B(("✅ " if margin is None else "") + "По умолчанию", callback_data=self.cb("trmg", "-")))
        kb.row(B(f"🚀 Опубликовать ({len(services)} усл.)", callback_data=self.cb("trgo")))
        text += ("\n\n💰 <b>Наценка</b> — сколько вы зарабатываете сверх цены сайта. 25% = при себестоимости "
                 "100 ₽ чистыми останется ~25 ₽ после комиссий.")
        return text, self.nav(kb, self.cb("trs", run["tid"], run["sid"]))

    def r_trmg(self, call: CallbackQuery, value: str) -> tuple:
        run = self.sess(call.from_user.id).get("run")
        if not run:
            return self.r_ml(call)
        run["margin"] = None if value == "-" else str(D(value))
        return self.scr_run_preview(call.from_user.id)

    def r_trmgc(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Наценка в % (например 25 или 37.5):", "run_margin", {},
                 self.cb("trmgback"))

    def r_trmgback(self, call: CallbackQuery, *args: str) -> tuple:
        if not self.sess(call.from_user.id).get("run"):
            return self.r_ml(call)
        return self.scr_run_preview(call.from_user.id)

    def i_run_margin(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        run = self.sess(uid).get("run")
        if not run:
            return self.r_ml(None)
        run["margin"] = str(D(Config.coerce("pct", text)))
        return self.scr_run_preview(uid)

    def r_trgo(self, call: CallbackQuery, *args: str) -> tuple:
        run = self.sess(call.from_user.id).get("run")
        if not run:
            return self.r_ml(call)
        kb = K().row(B("✅ Да, запустить", callback_data=self.cb("trgoy")),
                     B("Отмена", callback_data=self.cb("trmgback")))
        margin = f"{run['margin']}%" if run.get("margin") is not None else "по умолчанию"
        return (f"Запустить публикацию для {len(run.get('services', []))} услуг с наценкой {margin}?"
                f"{' (dry-run)' if self.p.dry else ''}", kb)

    def r_trgoy(self, call: CallbackQuery, *args: str) -> None:
        run = self.sess(call.from_user.id).pop("run", None)
        if not run:
            return None
        target = (call.message.chat.id, call.message.id)
        services = [s for s in (self.p.sup.service(run["sid"], x) for x in run.get("services", [])) if s]
        last = [0.0]

        def progress(i: int, total: int, rep: dict) -> None:
            if time.time() - last[0] < 3 and i < total:
                return
            last[0] = time.time()
            self.show(target, f"⏳ Публикация: {i}/{total}\nсоздано {rep['created']}, обновлено {rep['updated']}, "
                              f"пропущено {rep['skipped']}, ошибок {len(rep['errors'])}")

        def work() -> tuple:
            margin = D(run["margin"]) if run.get("margin") is not None else None
            rep = self.p.ml.run(run["tid"], run["sid"], services, progress, margin)
            text = (f"<b>Итог публикации</b>\nВсего: {rep['total']}\nСоздано: {rep['created']}\n"
                    f"Обновлено: {rep['updated']}\nПропущено: {rep['skipped']}\n"
                    f"Ошибки и пропуски с причиной: {len(rep['errors'])}")
            if rep["errors"]:
                text += "\n" + "\n".join(f"• {esc(e)}" for e in rep["errors"][:15])
            if rep["unknown"]:
                text += "\n⚠️ Неизвестные кодовые слова: " + ", ".join("{" + esc(u) + "}" for u in rep["unknown"])
            return text, self.nav(K().row(B("📋 Мои лоты", callback_data=self.cb("lots", 0))), None)

        self.bg(target, work, "⏳ Выставляю лоты…")
        return None

    # ── лоты ──
    def r_lx(self, call: CallbackQuery, lid: str) -> tuple:
        lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (int(lid),))
        return self.p.price.explain(lot), self.nav(K(), self.cb("l", lid))

    def r_lc(self, call: CallbackQuery, lid: str) -> tuple:
        cands = self.p.price.lot_candidates(int(lid), usable_only=False)
        lines = [f"<b>🧩 Кандидаты лота #{lid}</b>"]
        kb = K()
        for c in cands:
            rating, total = self.p.cat.rating(c["supplier_id"], c["service_id"])
            state = "⛔" if (c["disabled"] or not c["supplier_enabled"] or c["rate"] is None) else "✅"
            lines.append(f"{state}{'⭐' if c['is_primary'] else ''} {esc(c['supplier_name'])} / "
                         f"{esc(c['service_id'])} {esc((c['name'] or '')[:50])} — рейтинг {rating:.2f} ({total})")
            kb.row(B(f"⭐ {c['service_id']}", callback_data=self.cb("lcp", lid, c["supplier_id"], c["service_id"])),
                   B(f"❌ {c['service_id']}", callback_data=self.cb("lcr", lid, c["supplier_id"], c["service_id"])))
        kb.row(B("➕ Подсказки кандидатов", callback_data=self.cb("lca", lid)))
        lines.append("\n⭐ — основной (режим FIXED), ❌ — убрать. Добавить из каталога: карточка услуги → «Привязать».")
        return "\n".join(lines), self.nav(kb, self.cb("l", lid))

    def r_lcp(self, call: CallbackQuery, lid: str, sid: str, svc: str) -> tuple:
        self.p.db.execute("UPDATE lot_services SET is_primary=CASE WHEN supplier_id=? AND service_id=? THEN 1 ELSE 0 "
                          "END WHERE lot_id=?", (int(sid), svc, int(lid)))
        return self.r_lc(call, lid)

    def r_lcr(self, call: CallbackQuery, lid: str, sid: str, svc: str) -> tuple:
        self.p.db.execute("DELETE FROM lot_services WHERE lot_id=? AND supplier_id=? AND service_id=?",
                          (int(lid), int(sid), svc))
        return self.r_lc(call, lid)

    def r_lca(self, call: CallbackQuery, lid: str) -> tuple:
        lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (int(lid),))
        kb = K()
        for s in self.p.cat.suggest(lot):
            kb.row(B(f"{s['supplier_name'][:12]} {s['service_id']} {s['name'][:30]} ({s['score']})",
                     callback_data=self.cb("lcas", lid, s["supplier_id"], s["service_id"])))
        return "Подсказки по совпадению названия и категории:", self.nav(kb, self.cb("lc", lid))

    def r_lcas(self, call: CallbackQuery, lid: str, sid: str, svc: str) -> tuple:
        self.p.ml._ensure_candidate(int(lid), int(sid), svc)
        return self.r_lc(call, lid)

    def r_lmode(self, call: CallbackQuery, lid: str) -> tuple:
        kb = K()
        for m in SELECT_MODES:
            kb.row(B(m, callback_data=self.cb("lmd", lid, m)))
        kb.row(B("По умолчанию (категория/общий)", callback_data=self.cb("lmd", lid, "-")))
        return ("CHEAPEST — дешевле, QUALITY — по рейтингу, BALANCED — цена+рейтинг, FIXED — основной + запасные",
                self.nav(kb, self.cb("l", lid)))

    def r_lmd(self, call: CallbackQuery, lid: str, mode: str) -> tuple:
        self.p.db.execute("UPDATE lots SET mode=? WHERE id=?", (None if mode == "-" else mode, int(lid)))
        return self.scr_lot(int(lid), "✅ Режим сохранён.")

    def r_lm(self, call: CallbackQuery, lid: str) -> None:
        self.ask(call, call.from_user.id, "Маржа лота в % (или «-» — сбросить):", "lm", {"lid": int(lid)},
                 self.cb("l", lid))

    def i_lm(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        value = None if text == "-" else str(Config.coerce("pct", text))
        self.p.db.execute("UPDATE lots SET margin_override=? WHERE id=?", (value, data["lid"]))
        return self.scr_lot(data["lid"], "✅ Маржа сохранена. Цена обновится при следующей проверке.")

    def r_lp(self, call: CallbackQuery, lid: str) -> None:
        self.ask(call, call.from_user.id, "Ручная цена лота в ₽ (монитор цен не будет её менять):", "lp",
                 {"lid": int(lid)}, self.cb("l", lid))

    def i_lp(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        price = D(text, "-1")
        if price <= 0:
            raise ValueError("цена должна быть положительным числом")
        self.p.db.execute("UPDATE lots SET manual_price=? WHERE id=?", (str(price), data["lid"]))
        lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (data["lid"],))
        if lot["fp_lot_id"]:
            self.p.pmon.push_price(lot, price, "manual")
        return self.scr_lot(data["lid"], "✅ Ручная цена установлена.")

    def r_lpc(self, call: CallbackQuery, lid: str) -> tuple:
        self.p.db.execute("UPDATE lots SET manual_price=NULL WHERE id=?", (int(lid),))
        return self.scr_lot(int(lid), "✅ Ручная цена сброшена.")

    def r_lme(self, call: CallbackQuery, lid: str) -> tuple:
        self.p.db.execute("UPDATE lots SET manual_edit=0 WHERE id=?", (int(lid),))
        return self.scr_lot(int(lid), "✅ Отметка снята.")

    def r_lpush(self, call: CallbackQuery, lid: str) -> None:
        def work() -> tuple:
            lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (int(lid),))
            calc = self.p.price.calc_lot(lot)
            if not calc or not lot["fp_lot_id"]:
                return self.scr_lot(int(lid), "⚠️ Нет кандидатов или лот не опубликован.")
            ok = self.p.pmon.push_price(lot, calc["price"], "manual_push")
            return self.scr_lot(int(lid), "✅ Цена отправлена." if ok else "❌ Не удалось обновить цену.")
        self.bg(call, work)

    def r_le(self, call: CallbackQuery, lid: str) -> None:
        def work() -> tuple:
            lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (int(lid),))
            new = 0 if lot["enabled"] else 1
            if lot["fp_lot_id"] and not self.p.dry:
                self.p.ml.fp_update(int(lot["fp_lot_id"]), {"active": bool(new)})
            self.p.db.execute("UPDATE lots SET enabled=?, hidden_reason=? WHERE id=?",
                              (new, None if new else "manual", int(lid)))
            return self.scr_lot(int(lid), "✅ Лот включён." if new else "⏸ Лот выключен.")
        self.bg(call, work)

    def r_lr(self, call: CallbackQuery, lid: str) -> None:
        self.bg(call, lambda: self.scr_lot(int(lid), esc(self.p.ml.restore_lot(int(lid)))), "⏳ Восстанавливаю…")

    def r_ldel(self, call: CallbackQuery, lid: str) -> tuple:
        kb = K().row(B("Убрать из плагина", callback_data=self.cb("ldely", lid, 0)))
        kb.row(B("Убрать и удалить на FunPay", callback_data=self.cb("ldely", lid, 1)))
        kb.row(B("Отмена", callback_data=self.cb("l", lid)))
        return "Убрать лот из плагина? Заказы по нему перестанут обрабатываться.", kb

    def r_ldely(self, call: CallbackQuery, lid: str, fp: str) -> tuple:
        lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (int(lid),))
        if lot and int(fp) and lot["fp_lot_id"] and not self.p.dry:
            self.p.ml.fp_delete(int(lot["fp_lot_id"]))
        self.p.db.execute("DELETE FROM lot_services WHERE lot_id=?", (int(lid),))
        self.p.db.execute("DELETE FROM lots WHERE id=?", (int(lid),))
        return self.r_lots(call, "0")

    # ── заказы ──
    def order_list(self, rows: list[dict], page: int, act: str, title: str) -> tuple:
        kb = K()
        self.paginate(kb, rows, page,
                      lambda o: B(f"{STATUS_EMOJI.get(o['status'], '')}{'⚠️' if o['problem'] else ''} "
                                  f"#{o['fp_order_id']} {o['buyer'] or ''} {o['quantity']} шт.",
                                  callback_data=self.cb("od", o["id"])),
                      lambda pg: self.cb(act, pg))
        return f"<b>{title}</b>: {len(rows)}", self.nav(kb, self.cb("o"))

    def r_oa(self, call: CallbackQuery, page: str = "0") -> tuple:
        rows = self.p.db.query(f"SELECT * FROM orders WHERE status IN ({','.join('?' * len(ACTIVE_ORDER_STATUSES))}) ORDER BY id DESC",
                               ACTIVE_ORDER_STATUSES)
        return self.order_list(rows, int(page), "oa", "⏳ Активные заказы")

    def r_op(self, call: CallbackQuery, page: str = "0") -> tuple:
        rows = self.p.db.query("SELECT * FROM orders WHERE problem=1 AND status NOT IN ('CLOSED','REFUNDED') "
                               "ORDER BY id DESC")
        return self.order_list(rows, int(page), "op", "⚠️ Проблемные заказы")

    def r_ol(self, call: CallbackQuery, page: str = "0") -> tuple:
        rows = self.p.db.query("SELECT * FROM orders ORDER BY id DESC LIMIT 200")
        return self.order_list(rows, int(page), "ol", "📜 Последние заказы")

    def r_os(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Номер заказа FunPay (или ник покупателя):", "osearch", {}, self.cb("o"))

    def i_osearch(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        q = text.strip().lstrip("#")
        rows = self.p.db.query("SELECT * FROM orders WHERE fp_order_id=? OR buyer=? OR supplier_order_id=? "
                               "ORDER BY id DESC LIMIT 50", (q.upper(), q, q))
        if len(rows) == 1:
            return self.scr_order(rows[0]["id"])
        return self.order_list(rows, 0, "ol", f"🔍 «{esc(q)}»")

    def r_od(self, call: CallbackQuery, oid: str) -> tuple:
        return self.scr_order(int(oid))

    def r_oact(self, call: CallbackQuery, oid: str, action: str) -> None:
        self.bg(call, lambda: self.scr_order(int(oid), self.p.orders.manual(int(oid), action)))

    def r_ounc(self, call: CallbackQuery, oid: str) -> None:
        self.ask(call, call.from_user.id, "Номер заказа у поставщика (из его кабинета) — плагин продолжит "
                                          "отслеживать выполнение без повторной отправки:", "ounc",
                 {"oid": int(oid)}, self.cb("od", oid))

    def i_ounc(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        return self.scr_order(data["oid"], self.p.orders.manual(data["oid"], "set_sent", text.strip()))

    def r_oref(self, call: CallbackQuery, oid: str) -> tuple:
        o = self.p.orders.get(int(oid))
        kb = K().row(B("💸 Да, вернуть", callback_data=self.cb("oact", oid, "refund")),
                     B("Отмена", callback_data=self.cb("od", oid)))
        return f"Вернуть покупателю всю сумму {money(o['price_paid'])} ₽ по заказу #{esc(o['fp_order_id'])}?", kb

    def r_blo(self, call: CallbackQuery, oid: str) -> tuple:
        o = self.p.orders.get(int(oid))
        self.p.db.execute("INSERT OR REPLACE INTO blacklist(buyer, reason, ts) VALUES(?,?,?)",
                          (o["buyer"], f"заказ #{o['fp_order_id']}", now_ts()))
        return self.scr_order(int(oid), f"⛔ {esc(o['buyer'])} добавлен в чёрный список.")

    def r_bl(self, call: CallbackQuery, page: str = "0") -> tuple:
        rows = self.p.db.query("SELECT * FROM blacklist ORDER BY ts DESC")
        kb = K()
        self.paginate(kb, rows, int(page),
                      lambda r: B(f"❌ {r['buyer']} — {(r['reason'] or '')[:30]}",
                                  callback_data=self.cb("bldel", r["buyer"])),
                      lambda pg: self.cb("bl", pg))
        kb.row(B("➕ Добавить", callback_data=self.cb("bladd")))
        return f"<b>⛔ Чёрный список</b>: {len(rows)}\nНажмите на запись, чтобы удалить.", self.nav(kb, self.cb("o"))

    def r_bldel(self, call: CallbackQuery, buyer: str) -> tuple:
        self.p.db.execute("DELETE FROM blacklist WHERE buyer=?", (buyer,))
        return self.r_bl(call, "0")

    def r_bladd(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Ник покупателя и причина через «;» (например: <code>user123;спам</code>):",
                 "bladd", {}, self.cb("bl", 0))

    def i_bladd(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        buyer, _, reason = text.partition(";")
        self.p.db.execute("INSERT OR REPLACE INTO blacklist(buyer, reason, ts) VALUES(?,?,?)",
                          (buyer.strip(), reason.strip(), now_ts()))
        return self.r_bl(None, "0")

    # ── поднятие ──
    def r_r(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        on = self.p.cfg.get("raise.enabled")
        kb.row(B("⏸ Выключить" if on else "▶️ Включить", callback_data=self.cb("rt")),
               B("🚀 Поднять сейчас", callback_data=self.cb("rn")))
        kb.row(B(f"🌙 Ночная пауза: {'вкл' if self.p.cfg.get('raise.night_pause') else 'выкл'}",
                 callback_data=self.cb("rnight")))
        chosen = [int(x) for x in (self.p.cfg.get("raise.categories") or [])]
        for cat_id, name in self.p.raiser.categories():
            mark = "☑️" if not chosen or cat_id in chosen else "⬜"
            kb.row(B(f"{mark} {name[:40]}", callback_data=self.cb("rc", cat_id)))
        return self.p.raiser.status_text(), self.nav(kb, self.cb("m"))

    def r_rt(self, call: CallbackQuery, *args: str) -> tuple:
        self.p.cfg.set("raise.enabled", not self.p.cfg.get("raise.enabled"))
        return self.r_r(call)

    def r_rnight(self, call: CallbackQuery, *args: str) -> tuple:
        self.p.cfg.set("raise.night_pause", not self.p.cfg.get("raise.night_pause"))
        return self.r_r(call)

    def r_rc(self, call: CallbackQuery, cat_id: str) -> tuple:
        chosen = [int(x) for x in (self.p.cfg.get("raise.categories") or [])]
        all_ids = [c[0] for c in self.p.raiser.categories()]
        if not chosen:
            chosen = list(all_ids)
        cid = int(cat_id)
        chosen = [x for x in chosen if x != cid] if cid in chosen else chosen + [cid]
        self.p.cfg.set("raise.categories", [] if set(chosen) >= set(all_ids) else chosen)
        return self.r_r(call)

    def r_rn(self, call: CallbackQuery, *args: str) -> None:
        self.bg(call, lambda: (self.p.raiser.raise_now(), self.nav(K(), self.cb("r"))), "⏳ Поднимаю…")

    # ── поставщики ──
    def r_smode(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        for m in SELECT_MODES:
            kb.row(B(("✅ " if self.p.cfg.get("select_mode_default") == m else "") + m,
                     callback_data=self.cb("smodes", m)))
        return "Режим выбора поставщика по умолчанию:", self.nav(kb, self.cb("s"))

    def r_smodes(self, call: CallbackQuery, mode: str) -> tuple:
        self.p.cfg.set("select_mode_default", mode)
        return self.r_s(call)

    # мастер добавления сайта
    def r_sa(self, call: CallbackQuery, *args: str) -> None:
        self.sess(call.from_user.id)["sw"] = {}
        self.ask(call, call.from_user.id, "<b>Новый поставщик — шаг 1/7</b>\nНазвание сайта:", "sw_name", {},
                 self.cb("s"))

    def i_sw_name(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        self.sess(uid)["sw"] = {"name": text[:60]}
        kb = K()
        for key, preset in PRESETS.items():
            kb.row(B(preset["title"], callback_data=self.cb("swp", key)))
        kb.row(B("❌ Отмена", callback_data=self.cb("s")))
        return "<b>Шаг 2/7</b>\nВыберите пресет:", kb

    def r_swp(self, call: CallbackQuery, preset: str) -> None:
        sw = self.sess(call.from_user.id).setdefault("sw", {})
        sw["profile"] = deep_merge(PRESETS[preset]["profile"], {"name": sw.get("name", "Поставщик")})
        default = sw["profile"].get("base_url", "")
        prompt = "<b>Шаг 3/7</b>\nBase URL API (например https://site.com/api/v2):"
        if default and "example.com" not in default:
            prompt += f"\nПо умолчанию: <code>{esc(default)}</code> — отправьте «-», чтобы оставить."
        self.ask(call, call.from_user.id, prompt, "sw_url", {}, self.cb("s"))

    def i_sw_url(self, target: tuple, uid: int, text: str, data: dict) -> None:
        sw = self.sess(uid)["sw"]
        if text != "-":
            if not re.match(r"^https?://\S+$", text):
                self.ask(target, uid, "❗ URL должен начинаться с https://. Введите ещё раз:", "sw_url", {},
                         self.cb("s"))
                return None
            sw["profile"]["base_url"] = text.rstrip("/")
        self.ask(target, uid, "<b>Шаг 4/7</b>\nAPI-ключ (сообщение будет сразу удалено из чата):", "sw_key", {},
                 self.cb("s"))
        return None

    def i_sw_key(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        self.sess(uid)["sw"]["key"] = text
        kb = K()
        kb.row(*[B(c, callback_data=self.cb("swc", c)) for c in ("USD", "RUB", "EUR")])
        kb.row(B("❌ Отмена", callback_data=self.cb("s")))
        return "<b>Шаг 5/7</b>\nВалюта цен у сайта:", kb

    def r_swc(self, call: CallbackQuery, cur: str) -> tuple:
        self.sess(call.from_user.id)["sw"]["profile"]["currency"] = cur
        kb = K().row(B("за 1000 ед.", callback_data=self.cb("swr", 1000)), B("за 1 ед.", callback_data=self.cb("swr", 1)))
        kb.row(B("❌ Отмена", callback_data=self.cb("s")))
        return "Единица цены у сайта (rate указан за сколько единиц?):", kb

    def r_swr(self, call: CallbackQuery, unit: str) -> None:
        self.sess(call.from_user.id)["sw"]["profile"]["rate_unit"] = int(unit)
        self.r_swt(call)

    def test_profile(self, profile: dict, key: str) -> tuple[bool, str]:
        s = SupplierBase.create_from_profile(profile, key, 0, lambda: True)
        lines, ok = ["<b>Шаг 6/7 — тест подключения</b>"], True
        try:
            bal, cur = s.get_balance()
            lines.append(f"✅ Баланс: <b>{money(bal)} {esc(cur)}</b>")
        except SupplierError as e:
            ok = False
            lines.append(f"❌ Баланс: {esc(e.message)}")
            if s.last_raw:
                lines.append(f"Сырой ответ: <code>{esc(s.last_raw[:500])}</code>")
        try:
            items = s.get_services()
            if items:
                x = items[0]
                lines.append(f"✅ Найдено услуг: <b>{len(items)}</b>\nПример: {esc(x['service_id'])} "
                             f"{esc(x['name'][:70])} — {esc(x['rate'])} {esc(profile.get('currency'))}, "
                             f"мин {x['min']}, макс {x['max']}")
            else:
                ok = False
                lines.append(f"⚠️ Услуги не разобраны. Сырой ответ:\n<code>{esc(s.last_raw[:500])}</code>")
        except SupplierError as e:
            ok = False
            lines.append(f"❌ Каталог: {esc(e.message)}")
            if s.last_raw:
                lines.append(f"Сырой ответ: <code>{esc(s.last_raw[:500])}</code>")
        if not ok:
            lines.append("\nМожно сохранить (выключенным) и поправить маппинг в редакторе профиля.")
        return ok, "\n".join(lines)

    def r_swt(self, call: CallbackQuery, *args: str) -> None:
        sw = self.sess(call.from_user.id).get("sw") or {}
        if not sw.get("profile"):
            return None

        def work() -> tuple:
            ok, text = self.test_profile(sw["profile"], sw.get("key", ""))
            kb = K()
            kb.row(B("💾 Сохранить и включить" if ok else "💾 Сохранить (выключенным)", callback_data=self.cb("sws")))
            kb.row(B("🔁 Тест снова", callback_data=self.cb("swt")),
                   B("🛠 Сохранить и открыть редактор", callback_data=self.cb("swe")))
            kb.row(B("❌ Отмена", callback_data=self.cb("s")))
            sw["ok"] = ok
            return text, kb

        self.bg(call, work, "⏳ Тест подключения…")
        return None

    def _sw_save(self, uid: int) -> int:
        sw = self.sess(uid).pop("sw", {})
        errors = validate_profile(sw["profile"])
        sid = self.p.sup.add(sw["profile"], sw.get("key", ""), enabled=bool(sw.get("ok")) and not errors)
        if sw.get("ok"):
            try:
                self.p.sup.refresh_catalog(sid, force=True)
            except SupplierError as e:
                log_warn(f"Каталог после сохранения: {e.message}")
        return sid

    def r_sws(self, call: CallbackQuery, *args: str) -> tuple:
        sid = self._sw_save(call.from_user.id)
        return self.scr_sup(sid, "✅ <b>Шаг 7/7</b>: поставщик сохранён. Задайте приоритет при необходимости.")

    def r_swe(self, call: CallbackQuery, *args: str) -> tuple:
        sid = self._sw_save(call.from_user.id)
        return self.r_spe(call, str(sid))

    # карточка и редактор
    def r_spb(self, call: CallbackQuery, sid: str) -> None:
        def work() -> tuple:
            bal, cur = self.p.sup.balance(int(sid), max_age=0)
            return self.scr_sup(int(sid), f"💰 Баланс: {money(bal) + ' ' + esc(cur) if bal is not None else 'ошибка'}")
        self.bg(call, work)

    def r_spg(self, call: CallbackQuery, sid: str) -> None:
        def work() -> tuple:
            s = self.p.sup.get(int(sid))
            try:
                return self.scr_sup(int(sid), f"📶 Пинг: {s.ping()} мс")
            except SupplierError as e:
                return self.scr_sup(int(sid), f"📶 Ошибка: {esc(e.message)}")
        self.bg(call, work)

    def r_spt(self, call: CallbackQuery, sid: str) -> None:
        self.bg(call, lambda: (self.p.sup.test(int(sid)), self.nav(
            K().row(B("✏️ Редактор профиля", callback_data=self.cb("spe", sid))), self.cb("sp", sid))),
                "⏳ Тест подключения…")

    def r_spe(self, call: CallbackQuery, sid: str) -> tuple:
        kb = K()
        for i in range(0, len(SUPPLIER_EDIT_FIELDS), 2):
            kb.row(*[B(f[1], callback_data=self.cb("spf", sid, f[0])) for f in SUPPLIER_EDIT_FIELDS[i:i + 2]])
        kb.row(B("🧪 Тест снова", callback_data=self.cb("spt", sid)))
        return f"<b>✏️ Редактор профиля #{sid}</b>\nВыберите поле:", self.nav(kb, self.cb("sp", sid))

    def r_spf(self, call: CallbackQuery, sid: str, field: str) -> None:
        prof = self.p.sup.profile(int(sid))
        ftype = dict((f[0], f[2]) for f in SUPPLIER_EDIT_FIELDS)[field]
        if ftype == "secret":
            cur = "скрыт"
        elif ftype == "json":
            cur = json.dumps(prof.get(field, {}), ensure_ascii=False, indent=1)
        else:
            cur = str(prof.get(field, ""))
        prompt = f"Поле <b>{esc(field)}</b>. Текущее значение:\n<code>{esc(cur)[:2500]}</code>\n\nОтправьте новое"
        prompt += " (JSON-объект):" if ftype == "json" else ":"
        if ftype == "secret":
            prompt = "Отправьте новый API-ключ (сообщение будет удалено):"
        self.ask(call, call.from_user.id, prompt, "sp_field", {"sid": int(sid), "field": field}, self.cb("spe", sid))

    def i_sp_field(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        sid, field = data["sid"], data["field"]
        ftype = dict((f[0], f[2]) for f in SUPPLIER_EDIT_FIELDS)[field]
        if ftype == "secret":
            self.p.sup.set_key(sid, text)
            return self.scr_sup(sid, "✅ Ключ обновлён.")
        prof = self.p.sup.profile(sid)
        if ftype == "json":
            try:
                value = json.loads(text)
            except ValueError as e:
                return self.scr_sup(sid, f"❌ Неверный JSON: {esc(e)}")
            if not isinstance(value, dict):
                return self.scr_sup(sid, "❌ Нужен JSON-объект {…}")
        elif ftype == "int":
            value = int(D(text))
        elif ftype == "float":
            value = float(D(text))
        else:
            value = text.strip()
            if field in ("method", "currency"):
                value = value.upper()
            if field == "request_format":
                value = value.lower()
        prof[field] = value
        errors = validate_profile(prof)
        if errors:
            return self.scr_sup(sid, "❌ Профиль не сохранён:\n" + "\n".join(f"• {esc(e)}" for e in errors))
        if field == "name":
            self.p.sup.set_field(sid, "name", value)
        self.p.sup.update_profile(sid, prof)
        return self.scr_sup(sid, f"✅ Поле {esc(field)} сохранено. Нажмите «Тест», чтобы проверить.")

    def r_spprio(self, call: CallbackQuery, sid: str) -> None:
        self.ask(call, call.from_user.id, "Приоритет (меньше — выше):", "sp_prio", {"sid": int(sid)},
                 self.cb("sp", sid))

    def i_sp_prio(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        self.p.sup.set_field(data["sid"], "priority", int(D(text)))
        return self.scr_sup(data["sid"], "✅ Приоритет сохранён.")

    def r_spx(self, call: CallbackQuery, sid: str) -> tuple:
        r = self.p.sup.row(int(sid))
        if r["needs_key"] and not r["enabled"]:
            return self.scr_sup(int(sid), "🔑 Сначала введите API-ключ.")
        self.p.sup.set_field(int(sid), "enabled", 0 if r["enabled"] else 1)
        if not r["enabled"]:
            s = self.p.sup.get(int(sid))
            if s:
                s.breaker.reset()
        return self.scr_sup(int(sid))

    def r_spd(self, call: CallbackQuery, sid: str) -> tuple:
        new = self.p.sup.duplicate(int(sid))
        return self.scr_sup(new, "✅ Копия создана (выключена).")

    def r_spexp(self, call: CallbackQuery, sid: str) -> None:
        r = self.p.sup.row(int(sid))
        prof = self.p.sup.profile(int(sid))
        ensure_dirs()
        path = os.path.join(EXPORT_DIR, f"profile_{re.sub(r'[^A-Za-z0-9_-]', '_', r['name'])}.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(prof, f, ensure_ascii=False, indent=2)
        self.send_document(call.message.chat.id, path, f"Профиль {esc(r['name'])} (без ключа)")
        self.toast(call, "Профиль отправлен")

    def r_spdel(self, call: CallbackQuery, sid: str) -> tuple:
        n = self.p.sup.bound_lots(int(sid))
        kb = K().row(B("🗑 Да, удалить", callback_data=self.cb("spdely", sid)),
                     B("Отмена", callback_data=self.cb("sp", sid)))
        warn = f"\n⚠️ К поставщику привязано лотов: {n}. Их кандидаты от этого поставщика будут удалены." if n else ""
        return f"Удалить поставщика?{warn}", kb

    def r_spdely(self, call: CallbackQuery, sid: str) -> tuple:
        self.p.sup.delete(int(sid))
        return self.r_s(call)

    def r_simp(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Отправьте JSON-файл профиля поставщика документом:", "sup_import", {},
                 self.cb("s"), file=True)

    def f_sup_import(self, target: tuple, uid: int, path: str, data: dict) -> tuple:
        with open(path, "r", encoding="utf-8") as f:
            prof = json.load(f)
        errors = validate_profile(prof)
        if errors:
            return "❌ Профиль не прошёл проверку:\n" + "\n".join(f"• {esc(e)}" for e in errors), self.nav(K(),
                                                                                                         self.cb("s"))
        self.sess(uid)["simp"] = prof
        text = (f"<b>Превью профиля</b>\nНазвание: {esc(prof.get('name'))}\nURL: {esc(prof.get('base_url'))}\n"
                f"auth: {esc(prof['auth'].get('type'))}, формат {esc(prof.get('request_format'))}, "
                f"{esc(prof.get('method'))}\nВалюта: {esc(prof.get('currency'))} за {prof.get('rate_unit')}\n"
                f"Эндпоинтов: {len(prof.get('endpoints') or {})}\nПоставщик будет сохранён выключенным, "
                f"затем введите ключ.")
        kb = K().row(B("💾 Сохранить", callback_data=self.cb("simpy")), B("Отмена", callback_data=self.cb("s")))
        return text, kb

    def r_simpy(self, call: CallbackQuery, *args: str) -> tuple:
        prof = self.sess(call.from_user.id).pop("simp", None)
        if not prof:
            return self.r_s(call)
        sid = self.p.sup.add(prof, "", enabled=False, needs_key=True)
        return self.scr_sup(sid, "✅ Профиль импортирован. Введите ключ и включите поставщика.")

    # ── перенос лотов ──
    def r_tf(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K().row(B("⬇️ Экспорт", callback_data=self.cb("tfe")), B("⬆️ Импорт", callback_data=self.cb("tfi")),
                     B("🗂 Бэкапы", callback_data=self.cb("tfb")))
        return ("<b>📦 Перенос лотов</b>\nОбновление версии: Экспорт → установка новой версии → Импорт в режиме "
                "«Привязать к существующим лотам»."), self.nav(kb, self.cb("m"))

    def r_tfe(self, call: CallbackQuery, *args: str) -> tuple:
        opts = self.sess(call.from_user.id).setdefault("exp", {"keys": False, "stats": False, "bl": False})
        kb = K()
        kb.row(B(f"{'✅' if opts['keys'] else '⬜'} Включить ключи API", callback_data=self.cb("tfo", "keys")))
        kb.row(B(f"{'✅' if opts['stats'] else '⬜'} Включить статистику", callback_data=self.cb("tfo", "stats")))
        kb.row(B(f"{'✅' if opts['bl'] else '⬜'} Чёрный список и промокоды", callback_data=self.cb("tfo", "bl")))
        kb.row(B("⬇️ Создать экспорт", callback_data=self.cb("tfgo")))
        return ("<b>⬇️ Экспорт</b>\nКлючи API (если включены) шифруются паролем, который вы введёте.\n"
                "Активные заказы в экспорт не входят."), self.nav(kb, self.cb("tf"))

    def r_tfo(self, call: CallbackQuery, opt: str) -> tuple:
        opts = self.sess(call.from_user.id).setdefault("exp", {"keys": False, "stats": False, "bl": False})
        opts[opt] = not opts[opt]
        return self.r_tfe(call)

    def r_tfgo(self, call: CallbackQuery, *args: str) -> None:
        opts = self.sess(call.from_user.id).get("exp", {})
        if opts.get("keys"):
            self.ask(call, call.from_user.id, "Введите пароль для шифрования ключей (сообщение будет удалено):",
                     "exp_pw", {}, self.cb("tfe"))
            return None
        self.do_export(call, call.from_user.id, "")
        return None

    def i_exp_pw(self, target: tuple, uid: int, text: str, data: dict) -> None:
        if len(text) < 6:
            self.ask(target, uid, "❗ Пароль минимум 6 символов. Введите ещё раз:", "exp_pw", {}, self.cb("tfe"))
            return None
        self.do_export(target, uid, text)
        return None

    def do_export(self, target: Any, uid: int, password: str) -> None:
        opts = self.sess(uid).get("exp", {})
        chat_id = target.message.chat.id if isinstance(target, CallbackQuery) else target[0]

        def work() -> tuple:
            path, active = self.p.tr.export(bool(opts.get("keys")), bool(opts.get("stats")), bool(opts.get("bl")),
                                            password)
            self.send_document(chat_id, path, f"Экспорт AutoSMMway v{VERSION}")
            note = f"\nАктивных заказов не вошло в экспорт: {active}." if active else ""
            return f"✅ Экспорт отправлен документом.{note}", self.nav(K(), self.cb("tf"))

        self.bg(target, work, "⏳ Создаю экспорт…")

    def r_tfi(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Отправьте файл экспорта (.json или .zip) документом:", "imp_file", {},
                 self.cb("tf"), file=True)

    def f_imp_file(self, target: tuple, uid: int, path: str, data: dict) -> None:
        def work() -> tuple:
            try:
                doc = self.p.tr.load(path)
            except TransferError as e:
                return f"❌ Импорт невозможен: {esc(e)}", self.nav(K(), self.cb("tf"))
            text, stats = self.p.tr.preview(doc)
            self.sess(uid)["imp"] = {"doc": doc, "mode": "bind", "conflict": "keep", "password": "", "text": text,
                                     "stats": stats}
            return self.scr_import(uid)
        self.bg(target, work, "⏳ Проверяю файл…")

    def scr_import(self, uid: int) -> tuple:
        imp = self.sess(uid).get("imp")
        if not imp:
            return "Нет загруженного файла.", self.nav(K(), self.cb("tf"))
        modes = {"bind": "Привязать к существующим лотам", "bind_create": "Привязать и создать недостающие",
                 "settings": "Только настройки, поставщики, шаблоны"}
        kb = K()
        for m, title in modes.items():
            kb.row(B(("🔘 " if imp["mode"] == m else "⚪ ") + title, callback_data=self.cb("tfim", m)))
        kb.row(B(f"Конфликты: {'оставить текущее' if imp['conflict'] == 'keep' else 'взять из файла'}",
                 callback_data=self.cb("tfic")))
        if imp["stats"].get("has_keys"):
            kb.row(B(f"🔑 Пароль ключей: {'введён' if imp['password'] else 'нет'}", callback_data=self.cb("tfipw")))
        kb.row(B("✅ Применить", callback_data=self.cb("tfiy")))
        return imp["text"], self.nav(kb, self.cb("tf"))

    def r_tfim(self, call: CallbackQuery, mode: str) -> tuple:
        self.sess(call.from_user.id).get("imp", {})["mode"] = mode
        return self.scr_import(call.from_user.id)

    def r_tfic(self, call: CallbackQuery, *args: str) -> tuple:
        imp = self.sess(call.from_user.id).get("imp", {})
        imp["conflict"] = "file" if imp.get("conflict") == "keep" else "keep"
        return self.scr_import(call.from_user.id)

    def r_tfipw(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Пароль, которым шифровались ключи при экспорте:", "imp_pw", {},
                 self.cb("tfiback"))

    def r_tfiback(self, call: CallbackQuery, *args: str) -> tuple:
        return self.scr_import(call.from_user.id)

    def i_imp_pw(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        self.sess(uid).get("imp", {})["password"] = text
        return self.scr_import(uid)

    def r_tfiy(self, call: CallbackQuery, *args: str) -> tuple:
        imp = self.sess(call.from_user.id).get("imp")
        if not imp:
            return self.r_tf(call)
        kb = K().row(B("✅ Да, применить", callback_data=self.cb("tfiyy")),
                     B("Отмена", callback_data=self.cb("tfiback")))
        return "Перед применением будет создан автобэкап базы. Применить импорт?", kb

    def r_tfiyy(self, call: CallbackQuery, *args: str) -> None:
        imp = self.sess(call.from_user.id).pop("imp", None)
        if not imp:
            return None

        def work() -> tuple:
            rep = self.p.tr.apply(imp["doc"], imp["mode"], imp["conflict"], imp["password"])
            text = (f"<b>Отчёт импорта</b>\nПривязано: {rep['bound']}\nСоздано: {rep['created']}\n"
                    f"Пропущено: {rep['skipped']}\nНовых поставщиков: {rep['suppliers']}\n"
                    f"Новых шаблонов: {rep['templates']}\nИзменено настроек: {rep['settings']}\n"
                    f"Ошибок: {len(rep['errors'])}")
            if rep["errors"]:
                text += "\n" + "\n".join(f"• {esc(e)}" for e in rep["errors"][:15])
            kb = K().row(B("↩️ Откатить импорт", callback_data=self.cb("tfrb")))
            return text, self.nav(kb, self.cb("tf"))

        self.bg(call, work, "⏳ Применяю импорт…")
        return None

    def r_tfrb(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K().row(B("↩️ Да, откатить", callback_data=self.cb("tfrby")), B("Отмена", callback_data=self.cb("tf")))
        return "Восстановить базу из автобэкапа, сделанного перед импортом?", kb

    def r_tfrby(self, call: CallbackQuery, *args: str) -> tuple:
        return esc(self.p.tr.rollback()), self.nav(K(), self.cb("tf"))

    def r_tfb(self, call: CallbackQuery, *args: str) -> tuple:
        items = self.p.db.list_backups()[:int(self.p.cfg.get("backup_keep"))]
        lines = ["<b>🗂 Бэкапы</b>"]
        kb = K()
        for i, b in enumerate(items):
            lines.append(f"{i + 1}. {fmt_ts(b['ts'])} — {b['size'] // 1024} КБ, схема v{b['schema']}")
            kb.row(B(f"⬇️ Скачать #{i + 1}", callback_data=self.cb("tfbd", i)),
                   B(f"♻️ Восстановить #{i + 1}", callback_data=self.cb("tfbr", i)))
        kb.row(B("💾 Создать бэкап сейчас", callback_data=self.cb("tfbn")))
        return "\n".join(lines) if items else "Бэкапов пока нет.", self.nav(kb, self.cb("tf"))

    def r_tfbn(self, call: CallbackQuery, *args: str) -> tuple:
        self.p.db.backup("manual")
        return self.r_tfb(call)

    def r_tfbd(self, call: CallbackQuery, idx: str) -> None:
        items = self.p.db.list_backups()
        if int(idx) < len(items):
            self.send_document(call.message.chat.id, items[int(idx)]["path"], "Бэкап базы AutoSMMway")

    def r_tfbr(self, call: CallbackQuery, idx: str) -> tuple:
        kb = K().row(B("♻️ Да, восстановить", callback_data=self.cb("tfbry", idx)),
                     B("Отмена", callback_data=self.cb("tfb")))
        return "Восстановить базу из бэкапа? Перед этим будет сделан новый автобэкап.", kb

    def r_tfbry(self, call: CallbackQuery, idx: str) -> tuple:
        items = self.p.db.list_backups()
        if int(idx) >= len(items):
            return self.r_tfb(call)
        self.p.db.restore(items[int(idx)]["path"])
        self.p.sup.invalidate()
        return "✅ База восстановлена.", self.nav(K(), self.cb("tfb"))

    # ── настройки ──
    def r_sta(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        groups = list(SETTINGS_GROUPS.items())
        for i in range(0, len(groups), 2):
            kb.row(*[B(title, callback_data=self.cb("stg", g)) for g, title in groups[i:i + 2]])
        kb.row(B("✉️ Тексты сообщений", callback_data=self.cb("stmsg")))
        return ("<b>🔧 Все настройки</b>\nКомиссии не зашиты в код — сверяйте их с актуальными условиями FunPay.",
                self.nav(kb, self.cb("st")))

    @staticmethod
    def fmt_setting(value: Any, typ: str) -> str:
        if typ == "bool":
            return "вкл" if value else "выкл"
        if typ == "ids":
            return ", ".join(str(x) for x in value) or "авторизованные в Cardinal"
        return str(value)

    def r_stg(self, call: CallbackQuery, group: str) -> tuple:
        kb = K()
        for idx, (key, title, typ, g) in enumerate(SETTINGS_SCHEMA):
            if g != group:
                continue
            value = self.fmt_setting(self.p.cfg.get(key), typ)
            act = "stt" if typ == "bool" else "stk"
            kb.row(B(f"{title}: {value}"[:60], callback_data=self.cb(act, idx)))
        return f"<b>{SETTINGS_GROUPS.get(group, group)}</b>", self.nav(kb, self.cb("sta"))

    def r_stt(self, call: CallbackQuery, idx: str) -> tuple:
        key, _title, _typ, group = SETTINGS_SCHEMA[int(idx)]
        self.p.cfg.set(key, not self.p.cfg.get(key))
        if key in ("circuit_errors", "circuit_pause"):
            self.p.sup.invalidate()
        return self.r_stg(call, group)

    def r_stk(self, call: CallbackQuery, idx: str) -> None:
        key, title, typ, group = SETTINGS_SCHEMA[int(idx)]
        hint = ""
        if typ.startswith("choice:"):
            hint = "\nВарианты: " + ", ".join(typ.split(":", 1)[1].split("|"))
        elif typ == "time":
            hint = "\nФормат ЧЧ:ММ"
        self.ask(call, call.from_user.id, f"<b>{esc(title)}</b>\nТекущее: <code>{esc(self.p.cfg.get(key))}</code>{hint}"
                                          f"\nВведите новое значение:", "setting", {"idx": int(idx)},
                 self.cb("stg", group))

    def i_setting(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        key, title, typ, group = SETTINGS_SCHEMA[data["idx"]]
        try:
            value = Config.coerce(typ, text)
        except (ValueError, re.error) as e:
            return f"❌ Некорректное значение для «{esc(title)}»: {esc(e)}", self.nav(K(), self.cb("stg", group))
        self.p.cfg.set(key, value)
        self.p.cfg.validate()
        self.p.cfg.save()
        if key in ("circuit_errors", "circuit_pause"):
            self.p.sup.invalidate()
        if key.startswith("fx."):
            self.p.fx.cache.clear()
        return self.r_stg(None, group)

    def r_stmsg(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        items = list(MESSAGE_TITLES.items())
        for i in range(0, len(items), 2):
            kb.row(*[B(t, callback_data=self.cb("stm", k)) for k, t in items[i:i + 2]])
        return "<b>✉️ Тексты сообщений</b> (у каждого 2-3 варианта, выбор случайный)", self.nav(kb, self.cb("st"))

    def r_stm(self, call: CallbackQuery, key: str) -> tuple:
        variants = self.p.msg.variants(key)
        text = f"<b>{esc(MESSAGE_TITLES.get(key, key))}</b>\n\n" + "\n\n".join(
            f"<b>Вариант {i + 1}:</b>\n{esc(v)}" for i, v in enumerate(variants))
        text += "\n\nКодовые слова: " + " ".join("{" + k + "}" for k in MESSAGE_CODE_WORDS_HELP)
        kb = K().row(B("✏️ Изменить", callback_data=self.cb("stme", key)),
                     B("↩️ По умолчанию", callback_data=self.cb("stmr", key)))
        return text, self.nav(kb, self.cb("stmsg"))

    def r_stme(self, call: CallbackQuery, key: str) -> None:
        self.ask(call, call.from_user.id, "Отправьте варианты текста, разделяя их строкой <code>---</code>:",
                 "msg_edit", {"key": key}, self.cb("stm", key))

    def i_msg_edit(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        variants = [v.strip() for v in re.split(r"^\s*---\s*$", text, flags=re.M) if v.strip()]
        msgs = dict(self.p.cfg.get("messages") or {})
        msgs[data["key"]] = variants
        self.p.cfg.set("messages", msgs)
        return self.r_stm(None, data["key"])

    def r_stmr(self, call: CallbackQuery, key: str) -> tuple:
        msgs = dict(self.p.cfg.get("messages") or {})
        msgs[key] = list(DEFAULTS["messages"][key])
        self.p.cfg.set("messages", msgs)
        return self.r_stm(call, key)

    # ── отчёты и диагностика ──
    def r_rep(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K().row(B("Сегодня", callback_data=self.cb("rp", 1)), B("Неделя", callback_data=self.cb("rp", 7)),
                     B("Месяц", callback_data=self.cb("rp", 30)))
        return self.p.rep.period(1), self.nav(kb, self.cb("m"))

    def r_rp(self, call: CallbackQuery, days: str) -> tuple:
        kb = K().row(B("Сегодня", callback_data=self.cb("rp", 1)), B("Неделя", callback_data=self.cb("rp", 7)),
                     B("Месяц", callback_data=self.cb("rp", 30)))
        return self.p.rep.period(int(days)), self.nav(kb, self.cb("rep"))

    def r_dg(self, call: CallbackQuery, *args: str) -> None:
        kb = K().row(B("🔄 Обновить", callback_data=self.cb("dg")), B("🔁 Синхронизировать", callback_data=self.cb("sync")))
        self.bg(call, lambda: (self.p.rep.diagnostics(), self.nav(kb, self.cb("m"))), "⏳ Диагностика…")

    # ═══ Упрощённый интерфейс ═══

    def plugins_button(self, uid: Optional[int]) -> B:
        offset = self.sess(uid).get("plugins_offset", "0") if uid else "0"
        return B("◀️ К плагинам", callback_data=f"{CBT.PLUGINS_LIST}:{offset}")

    def scr_main(self, uid: Optional[int] = None) -> tuple[str, K]:
        p = self.p
        steps = self.setup_steps()
        done = sum(1 for s in steps if s[1])
        active = p.db.scalar(f"SELECT COUNT(*) FROM orders WHERE status IN "
                             f"({','.join('?' * len(ACTIVE_ORDER_STATUSES))})", ACTIVE_ORDER_STATUSES, 0)
        problems = p.db.scalar("SELECT COUNT(*) FROM orders WHERE problem=1 AND status NOT IN ('CLOSED','REFUNDED')",
                               (), 0)
        lots = p.db.scalar("SELECT COUNT(*) FROM lots WHERE fp_lot_id IS NOT NULL AND lost=0", (), 0)
        paused = p.db.scalar("SELECT COUNT(*) FROM lots WHERE auto_paused IS NOT NULL", (), 0)
        lines = [f"<b>🤖 AutoSMMway</b> v{VERSION}"]
        lines.append("🧪 Тестовый режим — ничего не отправляется по-настоящему" if p.dry else "✅ Работает")
        if done < len(steps):
            lines.append(f"⚙️ Настройка: {done}/{len(steps)} — нажмите «🚀 Начать»")
        lines.append(f"Лотов: {lots} | заказов в работе: {active}")
        if problems:
            lines.append(f"⚠️ Требуют внимания: {problems} — «🧾 Заказы»")
        if paused:
            lines.append(f"⏸ Лотов на паузе: {paused} — пополните баланс сайта, включатся сами")
        kb = K()
        if done < len(steps):
            kb.row(B("🚀 Начать (быстрая настройка)", callback_data=self.cb("go")))
        kb.row(B("🏷 Лоты", callback_data=self.cb("ml")), B("🧾 Заказы", callback_data=self.cb("o")))
        kb.row(B("🔌 Сайт", callback_data=self.cb("s")), B("📊 Статистика", callback_data=self.cb("bal")))
        kb.row(B("⚙️ Настройки", callback_data=self.cb("st")))
        kb.row(self.plugins_button(uid))
        return "\n".join(lines), kb

    # ── статистика ──
    def r_bal(self, call: CallbackQuery, *args: str) -> None:
        def work() -> tuple[str, K]:
            lines = ["<b>📊 Статистика</b>", "", "<b>Баланс сайтов:</b>"]
            for s in self.p.sup.list():
                if s["needs_key"]:
                    lines.append(f"🔑 {esc(s['name'])}: не подключён")
                    continue
                bal, cur = self.p.sup.balance(s["id"], max_age=0)
                lines.append(f"{'🟢' if s['enabled'] else '🔴'} {esc(s['name'])}: "
                             f"{money(bal) + ' ' + esc(cur) if bal is not None else 'нет ответа'}")
            for days in (1, 7, 30):
                lines.append("")
                lines.append(self.p.rep.period(days, short=True))
            return "\n".join(lines), self.nav(K().row(B("🔄 Обновить", callback_data=self.cb("bal"))), None)
        self.bg(call, work, "⏳ Считаю…")

    # ── настройки: только рычажки ──
    SIMPLE_TOGGLES = [
        ("auto.refund_on_fail", "Автовозврат денег, если заказ не выполнить"),
        ("auto.pause_lots_low_balance", "Пауза лотов, когда кончился баланс"),
        ("auto.auto_alternatives", "Запасной сайт, если основной не смог"),
        ("auto.confirm_auto_start", "Запускать без «+», если покупатель молчит"),
        ("auto.refill_requests", "Докрутка по просьбе покупателя"),
        ("raise.enabled", "Автоподнятие лотов"),
        ("loyalty.enabled", "Промокоды постоянным покупателям"),
        ("auto.notify_new_orders", "Уведомление о каждом заказе"),
    ]

    def r_st(self, call: CallbackQuery, *args: str) -> tuple:
        cfg = self.p.cfg
        kb = K()
        kb.row(B("✅ Боевой режим" if not self.p.dry else "🧪 Тестовый режим (нажмите — включить боевой)",
                 callback_data=self.cb("stdry")))
        kb.row(B(f"💰 Наценка: {cfg.get('margin_default'):g}%  (нажмите — изменить)", callback_data=self.cb("stmg")))
        for i, (key, title) in enumerate(self.SIMPLE_TOGGLES):
            kb.row(B(f"{'✅' if cfg.get(key) else '⬜'} {title}", callback_data=self.cb("sts", i)))
        kb.row(B("✉️ Тексты сообщений покупателям", callback_data=self.cb("stmsg")))
        return ("<b>⚙️ Настройки</b>\nНажмите на пункт: ✅ — включено, ⬜ — выключено.\n"
                "Всё остальное плагин настраивает сам."), self.nav(kb, None)

    def r_sts(self, call: CallbackQuery, idx: str) -> tuple:
        key = self.SIMPLE_TOGGLES[int(idx)][0]
        value = not self.p.cfg.get(key)
        self.p.cfg.set(key, value)
        if key == "auto.pause_lots_low_balance":
            self.p.cfg.set("auto.pause_lots_missing_service", value)
        if key == "raise.enabled" and value:
            self.p.cfg.set("raise.categories", [])
        return self.r_st(call)

    def r_stdry(self, call: CallbackQuery, *args: str) -> tuple:
        if self.p.dry:
            kb = K().row(B("✅ Да, включить", callback_data=self.cb("go4s", 0)),
                         B("Отмена", callback_data=self.cb("st")))
            return ("Включить боевой режим? Лоты начнут выставляться на FunPay, а заказы — уходить на сайт. "
                    "Перед этим пополните баланс сайта."), kb
        self.p.cfg.set("dry_run", True)
        return self.r_st(call)

    def r_stmg(self, call: CallbackQuery, *args: str) -> tuple:
        cur = float(self.p.cfg.get("margin_default"))
        kb = K()
        row = []
        for m in (10, 15, 20, 25, 30, 40, 50, 70, 100):
            row.append(B(("✅" if cur == m else "") + f"{m}%", callback_data=self.cb("stmgs", m)))
            if len(row) == 3:
                kb.row(*row)
                row = []
        return ("<b>💰 Наценка</b>\nСколько вы зарабатываете сверх цены сайта. Например, 25%: услуга за 100 ₽ "
                "продаётся примерно за 125 ₽ (+ комиссии).\nЦены всех лотов пересчитаются автоматически."), \
            self.nav(kb, self.cb("st"))

    def r_stmgs(self, call: CallbackQuery, value: str) -> tuple:
        self.p.cfg.set("margin_default", float(value))
        self.p.db.meta_set("setup_margin", 1)
        self.p.db.execute("UPDATE lots SET margin_override=NULL WHERE margin_override IS NOT NULL")
        threading.Thread(target=self.p.pmon.run_once, daemon=True, name="asm-reprice").start()
        self.toast(call, f"Наценка {value}% — цены обновляются")
        return self.r_st(call)

    # ── выставление лотов: пошагово, без кодовых слов ──
    def r_ml(self, call: CallbackQuery, *args: str) -> tuple:
        lots = self.p.db.scalar("SELECT COUNT(*) FROM lots WHERE lost=0", (), 0)
        kb = K()
        kb.row(B("➕ Выставить новые лоты", callback_data=self.cb("nl")))
        kb.row(B(f"📋 Мои лоты ({lots})", callback_data=self.cb("lots", 0)))
        return ("<b>🏷 Лоты</b>\n«Выставить новые лоты» — 4 простых шага кнопками. Тексты лотов, цены и "
                "категорию плагин подберёт сам."), self.nav(kb, None)

    def r_nl(self, call: CallbackQuery, *args: str) -> tuple:
        if not any(not s["needs_key"] for s in self.p.sup.list(enabled_only=True)):
            kb = K().row(B("🔌 Подключить сайт", callback_data=self.cb("go1")))
            return "Сначала подключите сайт, с которого брать услуги.", self.nav(kb, self.cb("ml"))
        self.sess(call.from_user.id)["nl"] = {}
        kb = K()
        for key, preset in TEMPLATE_PRESETS.items():
            if key == "universal":
                continue
            kb.row(B(preset["title"], callback_data=self.cb("nlp", key)))
        kb.row(B(TEMPLATE_PRESETS["universal"]["title"], callback_data=self.cb("nlp", "universal")))
        return "<b>Шаг 1 из 4.</b> Что будете продавать?", self.nav(kb, self.cb("ml"))

    def r_nlp(self, call: CallbackQuery, key: str) -> tuple:
        preset = TEMPLATE_PRESETS[key]
        nl = self.sess(call.from_user.id).setdefault("nl", {})
        nl.update({"preset": key})
        query = (preset.get("keywords") or [""])[0]
        subs = self.node_search(query, preset.get("node_hints")) if query else []
        kb = self.node_buttons(call.from_user.id, subs, "nln") if subs else K()
        kb.row(B("🔍 Найти другую категорию", callback_data=self.cb("nlq")))
        text = ("<b>Шаг 2 из 4.</b> В какую категорию FunPay выставить?\nПодходящие категории сверху — выберите "
                "нужную." if subs else "<b>Шаг 2 из 4.</b> Нажмите «Найти» и напишите название категории FunPay, "
                                       "например «instagram» или «tiktok».")
        return text, self.nav(kb, self.cb("nl"))

    def r_nlq(self, call: CallbackQuery, *args: str) -> None:
        self.ask(call, call.from_user.id, "Напишите название категории FunPay (например: <code>instagram</code>, "
                                          "<code>тикток</code>, <code>telegram</code>):", "nlq", {}, self.cb("nl"))

    def i_nlq(self, target: tuple, uid: int, text: str, data: dict) -> tuple:
        nums = re.findall(r"^\d+$", text.strip())
        if nums:
            sub = self.c.account.get_subcategory(SubCategoryTypes.COMMON, int(nums[0]))
            subs = [sub] if sub else []
        else:
            subs = self.node_search(text)
        if not subs:
            kb = K().row(B("🔍 Искать ещё раз", callback_data=self.cb("nlq")))
            return f"По «{esc(text)}» ничего не нашлось.", self.nav(kb, self.cb("nl"))
        kb = self.node_buttons(uid, subs, "nln")
        kb.row(B("🔍 Искать ещё раз", callback_data=self.cb("nlq")))
        return "<b>Шаг 2 из 4.</b> Выберите категорию FunPay:", self.nav(kb, self.cb("nl"))

    def _nl_template(self, preset_key: str, node: int) -> int:
        preset = TEMPLATE_PRESETS[preset_key]
        name = f"{preset['name']} [{node}]"
        t = self.p.db.one("SELECT id FROM templates WHERE name=?", (name,))
        if t:
            return t["id"]
        data = {k: preset[k] for k in MasterLot.TEMPLATE_FIELDS if k in preset}
        data.update({"name": name, "category_node": node})
        return self.p.ml.save_template(data)

    def r_nln(self, call: CallbackQuery, idx: str) -> tuple:
        uid = call.from_user.id
        res = self.sess(uid).get("node_results") or []
        nl = self.sess(uid).get("nl") or {}
        if int(idx) >= len(res) or not nl.get("preset"):
            return self.r_nl(call)
        node_id, name = res[int(idx)]
        nl.update({"node": int(node_id), "node_name": name, "tid": self._nl_template(nl["preset"], int(node_id))})
        sups = [s for s in self.p.sup.list(enabled_only=True) if not s["needs_key"]]
        if len(sups) == 1:
            return self.r_nls(call, str(sups[0]["id"]))
        kb = K()
        for s in sups:
            kb.row(B(f"🔌 {s['name']}", callback_data=self.cb("nls", s["id"])))
        return "С какого сайта брать услуги?", self.nav(kb, self.cb("nl"))

    def r_nls(self, call: CallbackQuery, sid: str, page: str = "0") -> Optional[tuple]:
        nl = self.sess(call.from_user.id).get("nl") or {}
        nl["sid"] = int(sid)
        if self.p.sup.catalog_age(int(sid)) is None:
            def work() -> tuple:
                self.p.sup.refresh_catalog(int(sid), force=True)
                return self.r_nls(call, sid, page)
            self.bg(call, work, "⏳ Загружаю услуги сайта…")
            return None
        cats = self.p.sup.categories(int(sid))
        preset = TEMPLATE_PRESETS.get(nl.get("preset"), {})
        keys = [norm_text(k) for k in preset.get("keywords") or []]
        hints = [norm_text(h) for h in preset.get("node_hints") or []]

        def score(name: str) -> int:
            n = norm_text(name)
            return (2 if any(k in n for k in keys) else 0) + (1 if any(h in n for h in hints) else 0)

        items = sorted(enumerate(cats), key=lambda it: -score(it[1]))
        if keys:
            matched = [it for it in items if score(it[1]) > 0]
            items = matched or items
        kb = K()
        self.paginate(kb, items, int(page),
                      lambda it: B(("🎯 " if score(it[1]) >= 3 else "") + it[1][:58],
                                   callback_data=self.cb("nlc", it[0])),
                      lambda pg: self.cb("nls", sid, pg))
        return ("<b>Шаг 3 из 4.</b> Выберите раздел услуг на сайте.\n🎯 — лучше всего подходит.\n"
                f"Категория FunPay: {esc(nl.get('node_name', ''))}"), self.nav(kb, self.cb("nl"))

    def r_nlc(self, call: CallbackQuery, idx: str) -> tuple:
        nl = self.sess(call.from_user.id).get("nl") or {}
        cats = self.p.sup.categories(nl["sid"])
        if int(idx) >= len(cats):
            return self.r_nl(call)
        nl["cat"] = int(idx)
        recs = self.p.ml.recommend(nl["sid"], cats[int(idx)], nl["tid"], n=3)
        nl["sel"] = [r["service_id"] for r in recs]
        nl["why"] = {r["service_id"]: r["why"] for r in recs}
        return self.scr_nl_services(call.from_user.id, 0)

    def scr_nl_services(self, uid: int, page: int) -> tuple:
        nl = self.sess(uid).get("nl") or {}
        cats = self.p.sup.categories(nl["sid"])
        cat = cats[nl["cat"]]
        t = self.p.ml.template(nl["tid"]) or {}
        unit = MasterLot.packs(t)[0] or self.p.ml.unit_for(t, 0)
        items = [s for s in self.p.sup.services(nl["sid"], category=cat, include_disabled=False)
                 if int(s["min"] or 1) <= unit <= int(s["max"] or 10 ** 9)]
        sel = nl.setdefault("sel", [])
        items.sort(key=lambda s: (s["service_id"] not in sel, D(s["rate"])))
        kb = K()

        def btn(s: dict) -> B:
            try:
                price = money(self.p.price.calc_service(nl["sid"], s, unit)["price"])
            except Exception:
                price = "?"
            mark = "✅" if s["service_id"] in sel else "⬜"
            return B(f"{mark} {price}₽ | {s['name'][:40]}", callback_data=self.cb("nlt", s["service_id"], page))

        self.paginate(kb, items, page, btn, lambda pg: self.cb("nlpg", pg))
        kb.row(B(f"➡️ Далее ({len(sel)} выбрано)", callback_data=self.cb("nlmg")))
        why = "\n".join(f"⭐ {esc(v)}" for k, v in (nl.get("why") or {}).items() if k in sel)
        return ("<b>Шаг 3 из 4.</b> Какие услуги выставить?\nЛучшие уже отмечены ✅ — можно оставить как есть. "
                f"Цена указана за {unit} шт. для покупателя.\n" + (f"\n{why}" if why else "")), \
            self.nav(kb, self.cb("nls", nl["sid"], 0))

    def r_nlpg(self, call: CallbackQuery, page: str) -> tuple:
        return self.scr_nl_services(call.from_user.id, int(page))

    def r_nlt(self, call: CallbackQuery, svc: str, page: str) -> tuple:
        nl = self.sess(call.from_user.id).get("nl") or {}
        sel = nl.setdefault("sel", [])
        if svc in sel:
            sel.remove(svc)
        else:
            sel.append(svc)
        return self.scr_nl_services(call.from_user.id, int(page))

    def r_nlmg(self, call: CallbackQuery, *args: str) -> tuple:
        nl = self.sess(call.from_user.id).get("nl") or {}
        if not nl.get("sel"):
            self.toast(call, "Отметьте хотя бы одну услугу", True)
            return self.scr_nl_services(call.from_user.id, 0)
        cur = nl.get("margin", self.p.cfg.get("margin_default"))
        kb = K()
        row = []
        for m in (15, 20, 25, 30, 40, 50):
            row.append(B(("✅" if float(cur) == m else "") + f"{m}%", callback_data=self.cb("nlms", m)))
            if len(row) == 3:
                kb.row(*row)
                row = []
        return ("<b>Шаг 4 из 4.</b> Какую наценку поставить?\n25% — услуга за 100 ₽ продаётся примерно за 125 ₽. "
                "Новичкам подходит 25-30%."), self.nav(kb, self.cb("nlpg", 0))

    def r_nlms(self, call: CallbackQuery, value: str) -> tuple:
        nl = self.sess(call.from_user.id).get("nl") or {}
        nl["margin"] = float(value)
        services = [s for s in (self.p.sup.service(nl["sid"], x) for x in nl["sel"]) if s]
        text = self.p.ml.preview(nl["tid"], nl["sid"], services, n=2, margin=D(value))
        text = re.sub(r"\n⚠️ Неизвестные кодовые слова:[^\n]*", "", text)
        kb = K().row(B(f"🚀 Выставить ({len(services)})", callback_data=self.cb("nlgo")))
        kb.row(B("✏️ Изменить выбор", callback_data=self.cb("nlpg", 0)))
        return "<b>Проверьте и выставляйте</b>\n" + text, self.nav(kb, self.cb("nlmg"))

    def r_nlgo(self, call: CallbackQuery, *args: str) -> None:
        nl = self.sess(call.from_user.id).pop("nl", None)
        if not nl:
            return None
        self.sess(call.from_user.id)["run"] = {"tid": nl["tid"], "sid": nl["sid"], "mode": "sel", "arg": nl["sel"],
                                               "services": list(nl["sel"]), "margin": str(D(nl["margin"]))}
        return self.r_trgoy(call)

    # ── мои лоты ──
    def r_lots(self, call: CallbackQuery, page: str = "0") -> tuple:
        lots = self.p.db.query("SELECT * FROM lots WHERE lost=0 ORDER BY id DESC")
        kb = K()

        def btn(l: dict) -> B:
            mark = "⏸" if l["auto_paused"] or not l["enabled"] else "🟢"
            return B(f"{mark} {l['price'] or '?'}₽ | {(l['title'] or '')[:40]}", callback_data=self.cb("l", l["id"]))

        self.paginate(kb, lots, int(page), btn, lambda pg: self.cb("lots", pg))
        kb.row(B("➕ Выставить ещё", callback_data=self.cb("nl")))
        return f"<b>📋 Мои лоты</b>: {len(lots)}\n🟢 продаётся ⏸ на паузе", self.nav(kb, self.cb("ml"))

    def scr_lot(self, lid: int, notice: str = "") -> tuple[str, K]:
        lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (lid,))
        if not lot:
            return "Лот не найден.", self.nav(K(), self.cb("lots", 0))
        try:
            calc = self.p.price.calc_lot(lot)
        except Exception:
            calc = None
        if lot["auto_paused"]:
            state = "⏸ на паузе: " + ("нет баланса на сайте" if lot["auto_paused"] == "balance" else
                                      "услуга недоступна на сайте") + " (включится сам)"
        else:
            state = "🟢 продаётся" if lot["enabled"] else "⏸ выключен вами"
        margin = lot["margin_override"] or self.p.cfg.get("margin_default")
        text = (f"{notice + chr(10) if notice else ''}<b>{esc((lot['title'] or '')[:150])}</b>\n"
                f"Состояние: {state}\nЦена: <b>{lot['price'] or '—'} ₽</b> | наценка {margin}%")
        if calc:
            text += f"\nС каждой продажи вы получаете ≈ <b>{money(calc['profit'])} ₽</b>"
        if lot["fp_lot_id"]:
            text += f"\nhttps://funpay.com/lots/offer?id={lot['fp_lot_id']}"
        kb = K()
        kb.row(B("⏸ Выключить" if lot["enabled"] else "▶️ Включить", callback_data=self.cb("le", lid)),
               B("💰 Наценка", callback_data=self.cb("lmg", lid)))
        kb.row(B("🧮 Как посчитана цена", callback_data=self.cb("lx", lid)),
               B("🗑 Удалить", callback_data=self.cb("ldel", lid)))
        return text, self.nav(kb, self.cb("lots", 0))

    def r_l(self, call: CallbackQuery, lid: str) -> tuple:
        return self.scr_lot(int(lid))

    def r_lmg(self, call: CallbackQuery, lid: str) -> tuple:
        kb = K()
        row = []
        for m in (10, 15, 20, 25, 30, 40, 50, 70, 100):
            row.append(B(f"{m}%", callback_data=self.cb("lmgs", lid, m)))
            if len(row) == 3:
                kb.row(*row)
                row = []
        kb.row(B("Как в настройках", callback_data=self.cb("lmgs", lid, "-")))
        return "Наценка для этого лота:", self.nav(kb, self.cb("l", lid))

    def r_lmgs(self, call: CallbackQuery, lid: str, value: str) -> None:
        self.p.db.execute("UPDATE lots SET margin_override=? WHERE id=?", (None if value == "-" else value, int(lid)))

        def work() -> tuple:
            lot = self.p.db.one("SELECT * FROM lots WHERE id=?", (int(lid),))
            calc = self.p.price.calc_lot(lot)
            if calc and lot["fp_lot_id"] and not lot["manual_price"]:
                self.p.pmon.push_price(lot, calc["price"], "margin")
            return self.scr_lot(int(lid), "✅ Наценка сохранена, цена обновлена.")
        self.bg(call, work)

    # ── сайт-поставщик ──
    def r_s(self, call: CallbackQuery, *args: str) -> tuple:
        kb = K()
        for s in self.p.sup.list():
            mark = "🔑" if s["needs_key"] else ("🟢" if s["enabled"] else "🔴")
            kb.row(B(f"{mark} {s['name']}", callback_data=self.cb("sp", s["id"])))
        kb.row(B("➕ Подключить сайт", callback_data=self.cb("go1")))
        return ("<b>🔌 Сайты</b>\n🟢 работает 🔴 выключен 🔑 нужен ключ\n\n"
                "💡 Можно подключить два сайта: если один не выполнит заказ, плагин сам отправит его на другой."), \
            self.nav(kb, None)

    def scr_sup(self, sid: int, notice: str = "") -> tuple[str, K]:
        r = self.p.sup.row(sid)
        if not r:
            return "Сайт не найден.", self.nav(K(), self.cb("s"))
        cached = self.p.sup._balances.get(sid)
        state = "🔑 нужен ключ" if r["needs_key"] else ("🟢 работает" if r["enabled"] else "🔴 выключен")
        text = (f"{notice + chr(10) if notice else ''}<b>🔌 {esc(r['name'])}</b>\nСостояние: {state}\n"
                f"Баланс: {money(cached[1]) + ' ' + esc(cached[2]) if cached else 'нажмите «Баланс»'}\n"
                f"Лотов с этого сайта: {self.p.sup.bound_lots(sid)}")
        if r["last_error"]:
            text += f"\n⚠️ Последняя ошибка: {esc(r['last_error'][:120])}"
        kb = K()
        kb.row(B("💰 Баланс", callback_data=self.cb("spb", sid)), B("🔑 Сменить ключ", callback_data=self.cb("spf", sid,
                                                                                                         "api_key")))
        kb.row(B("⏸ Выключить" if r["enabled"] else "▶️ Включить", callback_data=self.cb("spx", sid)),
               B("🗑 Удалить", callback_data=self.cb("spdel", sid)))
        if r["preset"] == "rest_custom":
            kb.row(B("🛠 Настройка API", callback_data=self.cb("spe", sid)))
        return text, self.nav(kb, self.cb("s"))

    def r_sp(self, call: CallbackQuery, sid: str) -> tuple:
        return self.scr_sup(int(sid))

    # ── заказы ──
    def r_o(self, call: CallbackQuery, *args: str) -> tuple:
        problems = self.p.db.scalar("SELECT COUNT(*) FROM orders WHERE problem=1 AND status NOT IN "
                                    "('CLOSED','REFUNDED')", (), 0)
        kb = K()
        if problems:
            kb.row(B(f"⚠️ Требуют внимания ({problems})", callback_data=self.cb("op", 0)))
        kb.row(B("⏳ В работе", callback_data=self.cb("oa", 0)), B("📜 Все", callback_data=self.cb("ol", 0)))
        kb.row(B("🔍 Найти по номеру", callback_data=self.cb("os")))
        return ("<b>🧾 Заказы</b>\nПлагин сам принимает заказы, отправляет их на сайт и возвращает деньги, если "
                "что-то пошло не так. Сюда заглядывайте, только если есть «⚠️ Требуют внимания»."), \
            self.nav(kb, None)

    def scr_order(self, oid: int, notice: str = "") -> tuple[str, K]:
        o = self.p.orders.get(oid)
        if not o:
            return "Заказ не найден.", self.nav(K(), self.cb("o"))
        svc = self.p.orders.primary_service(o)
        profit = self.p.price.profit(D(o["price_paid"]), D(o["cost"])) if o["cost"] and \
            o["status"] != ORDER_REFUNDED else None
        status = self.p.msg.status_text(o)
        text = (f"{notice + chr(10) if notice else ''}<b>{STATUS_EMOJI.get(o['status'], '')} Заказ "
                f"#{esc(o['fp_order_id'])}</b> — {esc(status)}\n"
                f"Покупатель: {esc(o['buyer'])}\nУслуга: {esc((svc or {}).get('name', '—'))[:80]}\n"
                f"Ссылка: {esc(o['link'] or '—')}\nКоличество: {o['quantity']}"
                f"{' | осталось ' + str(o['remain']) if o['remain'] else ''}\n"
                f"Оплачено: {money(o['price_paid'])} ₽" + (f" | прибыль {money(profit)} ₽" if profit is not None
                                                           else ""))
        if o["problem"] and o["error"]:
            reason = REFUND_REASONS.get(o["error"], ("", o["error"]))[1]
            text += f"\n⚠️ {esc(reason)}"
        if o["status"] == ORDER_UNCERTAIN:
            text += ("\n\n❓ Связь с сайтом оборвалась при отправке — заказ мог создаться. Проверьте в кабинете "
                     "сайта, есть ли заказ на эту ссылку.")
        kb = K()
        if o["status"] == ORDER_UNCERTAIN:
            kb.row(B("✅ Есть на сайте — ввести номер", callback_data=self.cb("ounc", oid)))
            kb.row(B("🔁 Нет на сайте — отправить", callback_data=self.cb("oact", oid, "resend")))
        elif o["status"] in (ORDER_FAILED, ORDER_PARTIAL) or (o["problem"] and o["status"] != ORDER_IN_PROGRESS):
            kb.row(B("🔁 Отправить ещё раз", callback_data=self.cb("oact", oid, "retry")))
        if o["status"] not in (ORDER_REFUNDED, ORDER_CLOSED):
            kb.row(B("💸 Вернуть деньги", callback_data=self.cb("oref", oid)),
                   B("✅ Закрыть", callback_data=self.cb("oact", oid, "close")))
        kb.row(B("🔄 Обновить", callback_data=self.cb("od", oid)))
        return text, self.nav(kb, self.cb("o"))


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# N. REPORTS/ALERTS: дайджест, алерты, диагностика
# ═══════════════════════════════════════════════════════════════════════════════════════════════

class Alerts:
    """Уведомления админам с подавлением повторов."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.sent: dict[str, float] = {}
        self.lock = threading.Lock()

    def send(self, text: str, key: Optional[str] = None, kb: Optional[K] = None,
             cooldown: Optional[int] = None) -> None:
        """Отправляет алерт; повтор с тем же key не чаще cooldown (по умолчанию из настроек)."""
        if key:
            cd = cooldown if cooldown is not None else int(self.p.cfg.get("alerts.cooldown_min")) * 60
            with self.lock:
                if time.time() - self.sent.get(key, 0) < cd:
                    return
                self.sent[key] = time.time()
        log_warn("ALERT: " + re.sub(r"<[^>]+>", "", text).replace("\n", " ")[:300])
        tg = self.p.c.telegram
        if not tg:
            return
        for admin in self.p.cfg.admin_ids(self.p.c):
            try:
                tg.bot.send_message(admin, f"<b>AutoSMMway</b>\n{text}"[:4000], parse_mode="HTML", reply_markup=kb,
                                    disable_web_page_preview=True)
            except Exception:
                log_error(f"Не удалось отправить алерт админу {admin}", exc=True)


class AutoPilot:
    """Автоматизация без участия продавца: пауза/включение лотов, запасные поставщики, автобэкап."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.force = threading.Event()
        self.last_guard = 0.0

    def on_no_balance(self, sid: int) -> None:
        row = self.p.sup.row(sid)
        self.p.alerts.send(f"💰 <b>{esc(row['name'] if row else sid)}</b>: не хватает баланса для заказа. "
                           f"Пополните баланс — лоты, которые нечем выполнить, встанут на паузу и включатся сами "
                           f"после пополнения.", key=f"nobal:{sid}", cooldown=1800)
        self.force.set()

    def lot_state(self, lot: dict) -> Optional[str]:
        """None — лот можно продавать; 'balance' — у всех поставщиков мало денег; 'service' — нет доступных услуг."""
        unit = self.p.price.lot_unit(lot)
        has_service = False
        for c in self.p.price.lot_candidates(lot["id"]):
            if not (int(c["min"] or 1) <= unit <= int(c["max"] or 10 ** 9)):
                continue
            s = self.p.sup.get(c["supplier_id"])
            if not s or not s.api_key:
                continue
            has_service = True
            bal, _cur = self.p.sup.balance(c["supplier_id"], max_age=600)
            if bal is None:
                return None
            if bal >= D(c["rate"]) * D(unit) / D(s.rate_unit):
                return None
        return "balance" if has_service else "service"

    def guard_lots(self) -> dict:
        """Ставит на паузу лоты, которые нечем выполнить, и включает обратно, когда проблема ушла."""
        res = {"paused": 0, "resumed": 0, "balance": 0, "service": 0}
        want_balance = self.p.cfg.get("auto.pause_lots_low_balance")
        want_service = self.p.cfg.get("auto.pause_lots_missing_service")
        lots = self.p.db.query("SELECT * FROM lots WHERE enabled=1 AND lost=0 AND fp_lot_id IS NOT NULL")
        for lot in lots:
            if self.p.stop.is_set():
                break
            try:
                state = self.lot_state(lot)
            except Exception:
                log_error(f"AutoPilot: лот {lot['id']}", exc=True)
                continue
            if state == "balance" and not want_balance or state == "service" and not want_service:
                state = None
            if state and not lot["auto_paused"]:
                if self._set_active(lot, False):
                    self.p.db.execute("UPDATE lots SET auto_paused=? WHERE id=?", (state, lot["id"]))
                    res["paused"] += 1
                    res[state] += 1
            elif not state and lot["auto_paused"]:
                if self._set_active(lot, True):
                    self.p.db.execute("UPDATE lots SET auto_paused=NULL WHERE id=?", (lot["id"],))
                    res["resumed"] += 1
        if res["paused"]:
            self.p.alerts.send(f"⏸ Автопауза лотов: {res['paused']} (нет баланса: {res['balance']}, нет услуги: "
                               f"{res['service']}). Они включатся автоматически, когда проблема исчезнет.",
                               key="autopause", cooldown=1800)
        if res["resumed"]:
            self.p.alerts.send(f"▶️ Лоты снова активны: {res['resumed']}.", key="autoresume", cooldown=600)
        return res

    def _set_active(self, lot: dict, active: bool) -> bool:
        if self.p.dry:
            log_info(f"[DRY-RUN] Лот FP {lot['fp_lot_id']}: {'включить' if active else 'пауза'}")
            return True
        try:
            self.p.ml.fp_update(int(lot["fp_lot_id"]), {"active": active})
            time.sleep(float(self.p.cfg.get("fp_pause")))
            log_info(f"Лот FP {lot['fp_lot_id']}: {'включён' if active else 'автопауза'}")
            return True
        except Exception as e:
            log_error(f"Не удалось {'включить' if active else 'выключить'} лот {lot['fp_lot_id']}: {e}")
            return False

    def attach_alternatives(self, lot: dict, limit: int = 2) -> int:
        """Добавляет лоту запасных поставщиков с похожей услугой (та же платформа, схожее название)."""
        min_score = float(self.p.cfg.get("auto.alt_min_score"))
        unit = self.p.price.lot_unit(lot)
        bound = self.p.price.lot_candidates(lot["id"], usable_only=False)
        have_suppliers = {b["supplier_id"] for b in bound}
        added = 0
        for s in self.p.cat.suggest(lot, limit=30):
            if added >= limit:
                break
            if s["score"] < min_score or s["supplier_id"] in have_suppliers:
                continue
            if not (int(s["min"] or 1) <= unit <= int(s["max"] or 10 ** 9)):
                continue
            base = bound[0] if bound else None
            if base and to_bool(base.get("refill")) and not to_bool(s.get("refill")):
                continue
            self.p.ml._ensure_candidate(lot["id"], s["supplier_id"], s["service_id"])
            have_suppliers.add(s["supplier_id"])
            added += 1
        return added

    def alternatives_pass(self) -> int:
        if not self.p.cfg.get("auto.auto_alternatives") or len(self.p.sup.list(enabled_only=True)) < 2:
            return 0
        total = 0
        for lot in self.p.db.query("SELECT * FROM lots WHERE enabled=1 AND lost=0"):
            if len(self.p.price.lot_candidates(lot["id"], usable_only=False)) < 2:
                total += self.attach_alternatives(lot)
        if total:
            self.p.alerts.send(f"🧩 Автоподбор: добавлено запасных поставщиков — {total}. При отказе основного "
                               f"заказ уйдёт запасному автоматически.", key="alts", cooldown=3600)
        return total

    def step(self) -> int:
        """Проход автопилота; возвращает паузу до следующего (с)."""
        now = time.time()
        if self.force.is_set() or now - self.last_guard > 600:
            self.force.clear()
            self.last_guard = now
            self.guard_lots()
        if now - float(self.p.db.meta_get("auto_alts_ts", 0)) > 6 * 3600:
            self.p.db.meta_set("auto_alts_ts", int(now))
            self.alternatives_pass()
        today = datetime.now().strftime("%Y-%m-%d")
        if self.p.cfg.get("auto.daily_backup") and self.p.db.meta_get("auto_backup_day") != today:
            self.p.db.meta_set("auto_backup_day", today)
            self.p.db.backup("daily")
        return 60 if not self.force.is_set() else 5


class Reports:
    """Отчёты, дайджест, проверки балансов, диагностика."""

    def __init__(self, p: "AutoSMM"):
        self.p = p
        self.last_balance_check = 0

    def _orders(self, days: int) -> list[dict]:
        if days == 1:
            start = int(datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
        else:
            start = now_ts() - days * 86400
        return self.p.db.query("SELECT * FROM orders WHERE created_at>=?", (start,))

    def period(self, days: int, short: bool = False) -> str:
        """Оборот, чистая прибыль, заказы, доля возвратов, топ-5/убыточные лоты, расход по поставщикам."""
        orders = self._orders(days)
        title = {1: "сегодня", 7: "неделя", 30: "месяц"}.get(days, f"{days} дн.")
        revenue = Decimal("0")
        profit = Decimal("0")
        refunded = 0
        by_lot: dict[int, Decimal] = {}
        by_sup: dict[int, Decimal] = {}
        for o in orders:
            paid = D(o["price_paid"])
            if o["status"] == ORDER_REFUNDED:
                refunded += 1
                continue
            revenue += paid - D(o["refunded_amount"])
            if o["cost"]:
                pr = self.p.price.profit(paid - D(o["refunded_amount"]), D(o["cost"]))
                profit += pr
                by_lot[o["lot_id"]] = by_lot.get(o["lot_id"], Decimal("0")) + pr
                by_sup[o["supplier_id"]] = by_sup.get(o["supplier_id"], Decimal("0")) + D(o["cost"])
        n = len(orders)
        text = (f"<b>📊 Отчёт: {title}</b>\nЗаказов: {n} | оборот {money(revenue)} ₽ | чистая прибыль "
                f"{money(profit)} ₽ | возвраты {refunded / n * 100 if n else 0:.1f}%")
        if short:
            return text
        top = sorted(by_lot.items(), key=lambda x: -x[1])[:5]
        losing = [x for x in by_lot.items() if x[1] < 0]
        if top:
            text += "\n\n<b>Топ-5 лотов:</b>"
            for lid, pr in top:
                lot = self.p.db.one("SELECT title FROM lots WHERE id=?", (lid,))
                text += f"\n#{lid} {esc(((lot or {}).get('title') or '')[:40])}: {money(pr)} ₽"
        if losing:
            text += "\n\n<b>Убыточные лоты:</b>"
            for lid, pr in losing[:10]:
                lot = self.p.db.one("SELECT title FROM lots WHERE id=?", (lid,))
                text += f"\n#{lid} {esc(((lot or {}).get('title') or '')[:40])}: {money(pr)} ₽"
        if by_sup:
            text += "\n\n<b>Расход по поставщикам:</b>"
            for sid, cost in by_sup.items():
                row = self.p.sup.row(sid) if sid else None
                text += f"\n{esc(row['name'] if row else sid)}: {money(cost)} ₽"
        return text

    def check_balances(self) -> list[str]:
        warnings = []
        threshold = D(self.p.cfg.get("alerts.balance_threshold"))
        for s in self.p.sup.list(enabled_only=True):
            bal, cur = self.p.sup.balance(s["id"], max_age=600)
            if bal is None:
                warnings.append(f"{s['name']}: баланс недоступен")
                self.p.alerts.send(f"📡 API <b>{esc(s['name'])}</b> недоступно: {esc(s['last_error'] or '')}",
                                   key=f"api:{s['id']}")
            elif bal < threshold:
                warnings.append(f"{s['name']}: баланс {money(bal)} {cur}")
                self.p.alerts.send(f"💰 Низкий баланс <b>{esc(s['name'])}</b>: {money(bal)} {esc(cur)}",
                                   key=f"bal:{s['id']}")
        return warnings

    def error_series(self) -> None:
        limit = int(self.p.cfg.get("alerts.error_series"))
        rows = self.p.db.query("SELECT event FROM order_events WHERE event IN ('supplier_fail','sent','poll_error') "
                               "ORDER BY id DESC LIMIT ?", (limit,))
        if limit and len(rows) >= limit and all(r["event"] != "sent" for r in rows):
            self.p.alerts.send(f"🧯 Серия ошибок поставщиков: последние {limit} событий — ошибки.", key="err_series")

    def digest_text(self) -> str:
        text = "<b>☀️ Ежедневный дайджест</b>\n" + self.period(1, short=True).split("\n", 1)[1]
        text += "\n" + self.period(7)
        lines = []
        for s in self.p.sup.list(enabled_only=True):
            bal, cur = self.p.sup.balance(s["id"], max_age=0)
            lines.append(f"{esc(s['name'])}: {money(bal) + ' ' + esc(cur) if bal is not None else 'ошибка'}")
        if lines:
            text += "\n\n<b>Балансы:</b>\n" + "\n".join(lines)
        warnings = []
        problems = self.p.db.scalar("SELECT COUNT(*) FROM orders WHERE problem=1 AND status NOT IN "
                                    "('CLOSED','REFUNDED')", (), 0)
        if problems:
            warnings.append(f"проблемных заказов: {problems}")
        need_key = [s["name"] for s in self.p.sup.list() if s["needs_key"]]
        if need_key:
            warnings.append("нужен ключ: " + ", ".join(need_key))
        lost = self.p.db.scalar("SELECT COUNT(*) FROM lots WHERE lost=1", (), 0)
        if lost:
            warnings.append(f"потерянных лотов: {lost}")
        if self.p.dry:
            warnings.append("включён dry-run")
        if warnings:
            text += "\n\n<b>⚠️ Предупреждения:</b>\n" + "\n".join(f"• {esc(w)}" for w in warnings)
        return text

    def diagnostics(self) -> str:
        p = self.p
        lines = [f"<b>🛠 Диагностика AutoSMMway v{VERSION}</b>",
                 f"Схема БД: v{p.db.schema_version()} (ожидается v{SCHEMA_VERSION})",
                 f"Папка данных: <code>{esc(os.path.abspath(DATA_DIR))}</code>",
                 f"Dry-run: {'ВКЛ' if p.dry else 'выкл'}"]
        if D(p.cfg.get("fp_fee")) == 0 and D(p.cfg.get("withdraw_fee")) == 0:
            lines.append("⚠️ Комиссии FP и вывода равны 0 — проверьте настройки.")
        lines.append("\n<b>Поставщики:</b>")
        for s in p.sup.list():
            if s["needs_key"]:
                lines.append(f"🔑 {esc(s['name'])}: нужен ключ")
                continue
            inst = p.sup.get(s["id"])
            try:
                ms = inst.ping()
                state = f"{ms} мс"
            except SupplierError as e:
                state = f"ошибка: {esc(e.message)}"
            br = " ⛔ breaker" if inst.breaker.is_open else ""
            lines.append(f"{'🟢' if s['enabled'] else '🔴'} {esc(s['name'])}: {state}{br}")
        counts = p.db.query(f"SELECT status, COUNT(*) AS cnt FROM orders WHERE status IN "
                            f"({','.join('?' * len(ACTIVE_ORDER_STATUSES))}) GROUP BY status",
                            ACTIVE_ORDER_STATUSES)
        lines.append("\n<b>Очередь заказов:</b> " + (", ".join(f"{r['status']}={r['cnt']}" for r in counts) or "пусто"))
        nxt = p.db.scalar("SELECT MIN(next_at) FROM raise_state", ())
        lines.append(f"Автоподнятие: {'вкл' if p.cfg.get('raise.enabled') else 'выкл'}; следующее через "
                     f"{fmt_duration(int(nxt) - now_ts()) if nxt else '—'}")
        if p.c.autoraise_enabled and p.cfg.get("raise.enabled"):
            lines.append("⚠️ Конфликт: в Cardinal включено своё автоподнятие (autoRaise). Отключите одно из двух.")
        fx_ts = p.db.meta_get("fx:USD:ts")
        lines.append(f"Курс USD: {p.db.meta_get('fx:USD', '—')} (обновлён {fmt_ts(int(fx_ts)) if fx_ts else '—'}, "
                     f"источник {p.cfg.get('fx.source')})")
        last_sync = p.db.meta_get("last_sync")
        lines.append(f"Последняя синхронизация: {fmt_ts(int(last_sync)) if last_sync else '—'}")
        lines.append(f"Монитор цен: последний проход {fmt_ts(p.pmon.last_run) if p.pmon.last_run else '—'}")
        alive = [t.name for t in p.threads if t.is_alive()]
        lines.append(f"Потоки: {', '.join(alive) or 'не запущены'}")
        return "\n".join(lines)

    def step(self) -> int:
        """Дайджест по расписанию, балансы, серия ошибок."""
        if self.p.cfg.get("digest.enabled"):
            h, m = parse_hhmm(self.p.cfg.get("digest.time"))
            now = datetime.now()
            today = now.strftime("%Y-%m-%d")
            if (now.hour, now.minute) >= (h, m) and self.p.db.meta_get("last_digest") != today:
                self.p.db.meta_set("last_digest", today)
                self.p.alerts.send(self.digest_text())
        if time.time() - self.last_balance_check > 1800:
            self.last_balance_check = time.time()
            self.check_balances()
        self.error_series()
        return 60


# ═══════════════════════════════════════════════════════════════════════════════════════════════
# O. РЕГИСТРАЦИЯ ХЕНДЛЕРОВ И ЗАПУСК ФОНОВЫХ ПОТОКОВ
# ═══════════════════════════════════════════════════════════════════════════════════════════════

class AutoSMM:
    """Корневой объект плагина: связывает все модули."""

    def __init__(self, c: "Cardinal"):
        ensure_dirs()
        self.c = c
        self.stop = threading.Event()
        self.fp_lock = threading.RLock()
        self.threads: list[threading.Thread] = []
        self.started = False
        self.cfg = Config()
        self.db = Database(keep_backups=int(self.cfg.get("backup_keep")))
        self.alerts = Alerts(self)
        self.sup = SupplierManager(self)
        self.fx = FxRates(self)
        self.price = PriceEngine(self)
        self.pmon = PriceMonitor(self)
        self.cat = Catalog(self)
        self.ml = MasterLot(self)
        self.msg = Messenger(self)
        self.orders = OrderManager(self)
        self.raiser = Raiser(self)
        self.sync = SyncManager(self)
        self.tr = Transfer(self)
        self.rep = Reports(self)
        self.auto = AutoPilot(self)
        self.ui = TelegramUI(self)
        self._ensure_default_supplier()

    @property
    def dry(self) -> bool:
        return bool(self.cfg.get("dry_run"))

    def _ensure_default_supplier(self) -> None:
        """При первом запуске создаёт профиль SMMway без ключа (выключен до ввода ключа)."""
        if self.db.meta_get("initialized"):
            return
        if not self.sup.list():
            self.sup.add(dict(PRESETS["smmway"]["profile"]), "", enabled=False, needs_key=True)
        self.db.meta_set("initialized", now_ts())

    def _loop(self, name: str, fn: Callable[[], int]) -> None:
        log_info(f"Поток {name} запущен")
        while not self.stop.is_set():
            try:
                delay = fn()
            except Exception as e:
                log_error(f"Поток {name}: {e}", exc=True)
                delay = 30
            self.stop.wait(max(1, int(delay)))
        log_info(f"Поток {name} остановлен")

    def _orders_step(self) -> int:
        self.orders.tick()
        return 5

    def _prices_step(self) -> int:
        sids = {r["supplier_id"] for r in self.db.query("SELECT DISTINCT supplier_id FROM lot_services")}
        for sid in sids:
            row = self.sup.row(sid)
            if row and row["enabled"] and not row["needs_key"]:
                try:
                    self.sup.refresh_catalog(sid)
                except SupplierError as e:
                    log_warn(f"Каталог {row['name']}: {e.message}")
        self.pmon.run_once()
        return int(self.cfg.get("price_check_interval")) * 60

    def start_threads(self) -> None:
        """Запуск демон-потоков: заказы, цены, поднятие, дайджест/алерты."""
        if self.started:
            return
        self.started = True
        self.orders.restore()
        for name, fn in (("asm-orders", self._orders_step), ("asm-prices", self._prices_step),
                         ("asm-raise", self.raiser.step), ("asm-reports", self.rep.step),
                         ("asm-autopilot", self.auto.step)):
            t = threading.Thread(target=self._loop, args=(name, fn), daemon=True, name=name)
            t.start()
            self.threads.append(t)

    def initial_sync(self) -> None:
        try:
            self.sync.check_version()
            self.sync.run()
        except Exception as e:
            log_error(f"Стартовая синхронизация не удалась: {e}", exc=True)

    def shutdown(self) -> None:
        self.stop.set()


PLUGIN: Optional[AutoSMM] = None


def init(c: "Cardinal") -> None:
    """BIND_TO_PRE_INIT: база, конфиг, Telegram-интерфейс."""
    global PLUGIN
    try:
        PLUGIN = AutoSMM(c)
        PLUGIN.ui.register()
        log_info(f"v{VERSION} инициализирован (схема БД v{PLUGIN.db.schema_version()}, "
                 f"dry-run={'вкл' if PLUGIN.dry else 'выкл'})")
    except Exception as e:
        PLUGIN = None
        log_error(f"Ошибка инициализации: {e}", exc=True)


def post_start(c: "Cardinal") -> None:
    """BIND_TO_POST_START: аккаунт готов — синхронизация и фоновые потоки."""
    if not PLUGIN:
        return
    threading.Thread(target=PLUGIN.initial_sync, daemon=True, name="asm-sync").start()
    PLUGIN.start_threads()


def new_order_handler(c: "Cardinal", event: NewOrderEvent) -> None:
    """BIND_TO_NEW_ORDER."""
    if PLUGIN:
        PLUGIN.orders.handle_new_order(event)


def new_message_handler(c: "Cardinal", event: NewMessageEvent) -> None:
    """BIND_TO_NEW_MESSAGE."""
    if PLUGIN:
        PLUGIN.orders.handle_message(event)


def order_status_handler(c: "Cardinal", event: OrderStatusChangedEvent) -> None:
    """BIND_TO_ORDER_STATUS_CHANGED."""
    if PLUGIN:
        PLUGIN.orders.handle_status_changed(event)


def pre_stop(c: "Cardinal") -> None:
    """BIND_TO_PRE_STOP."""
    if PLUGIN:
        PLUGIN.shutdown()


def on_delete(c: "Cardinal", call: CallbackQuery) -> None:
    """BIND_TO_DELETE: останавливает потоки; данные в storage/plugins/autosmmway сохраняются."""
    if PLUGIN:
        PLUGIN.shutdown()
        PLUGIN.db.backup("on_delete")
        PLUGIN.db.close()
    log_info("Плагин удалён. Данные оставлены в " + os.path.abspath(DATA_DIR))


BIND_TO_PRE_INIT = [init]
BIND_TO_POST_START = [post_start]
BIND_TO_NEW_ORDER = [new_order_handler]
BIND_TO_NEW_MESSAGE = [new_message_handler]
BIND_TO_ORDER_STATUS_CHANGED = [order_status_handler]
BIND_TO_PRE_STOP = [pre_stop]
BIND_TO_DELETE = on_delete
