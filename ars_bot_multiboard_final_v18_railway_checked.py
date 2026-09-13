#!/usr/bin/env python3
"""
Premium Hub Digital Shop Bot — V15 supplier control + own-stock final build

Merged from the uploaded ARS balance bot and PayHub direct-payment bot.
Core goals:
- Forced channel/group membership gate
- Multi-board live products with admin ON/OFF controls
- Admin-created own-stock products with atomic inventory reservation
- PayHub balance top-ups (manual verify + webhook)
- Direct PayHub product checkout (manual verify + webhook)
- Atomic/idempotent payment processing to prevent double credit/delivery
- Supplier-aware delivery routing with safer delivery state machine
- Persistent delivery payload so a customer can retrieve a code/link again
- Admin statistics, pending/review queues, and broadcast

Required packages: requests, python-dotenv, flask
"""

from __future__ import annotations

import hmac
import hashlib
import json
import os
import re
import sqlite3
import threading
import time
import uuid
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from typing import Any, Dict, Iterable, Optional, Tuple

import requests
from dotenv import load_dotenv

load_dotenv()

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
API_KEY = os.getenv("API_KEY", "").strip()
BASE_URL = os.getenv("BASE_URL", "https://aiversehub.store").rstrip("/")

# Second supplier board: Elite Tools Store Reseller API
ELITE_BASE_URL = os.getenv(
    "ELITE_BASE_URL", "https://elite-tools-store.up.railway.app"
).rstrip("/")
ELITE_API_KEY = os.getenv("ELITE_API_KEY", "").strip()
ELITE_PRODUCTS_PATH = os.getenv("ELITE_PRODUCTS_PATH", "/api/reseller/products").strip()
ELITE_BALANCE_PATH = os.getenv("ELITE_BALANCE_PATH", "/api/reseller/balance").strip()
ELITE_ORDER_PATH = os.getenv("ELITE_ORDER_PATH", "/api/reseller/buy").strip()

PAYMENT_BASE_URL = os.getenv(
    "PAYMENT_BASE_URL", "https://payhub-railway-production.up.railway.app"
).rstrip("/")
PAYMENT_API_KEY = os.getenv("PAYMENT_API_KEY", "").strip()
PAYMENT_WEBHOOK_SECRET = os.getenv("PAYMENT_WEBHOOK_SECRET", "").strip()
WEBHOOK_HOST = os.getenv("WEBHOOK_HOST", "0.0.0.0")
WEBHOOK_PORT = int(os.getenv("PORT") or os.getenv("WEBHOOK_PORT", "8080"))

FORCE_CHANNEL = os.getenv("FORCE_CHANNEL", "@free_internet_config_bd").strip()
FORCE_GROUP = os.getenv("FORCE_GROUP", "@gemini_vr_Chat").strip()
FORCE_CHANNEL_URL = os.getenv(
    "FORCE_CHANNEL_URL", "https://t.me/free_internet_config_bd"
).strip()
FORCE_GROUP_URL = os.getenv(
    "FORCE_GROUP_URL", "https://t.me/gemini_vr_Chat"
).strip()
LOG_CHAT_ID = os.getenv("LOG_CHAT_ID", FORCE_GROUP).strip()
ADMIN_IDS = {
    x.strip()
    for x in os.getenv("ADMIN_IDS", "8908955171,5446536002").split(",")
    if x.strip()
}

MIN_TOPUP = Decimal("0.01")
# MARKUP_USDT remains the backwards-compatible default for both suppliers.
MARKUP_USDT = Decimal(os.getenv("MARKUP_USDT", "0.20"))
AIVERSE_MARKUP_USDT = Decimal(os.getenv("AIVERSE_MARKUP_USDT", str(MARKUP_USDT)))
ELITE_MARKUP_USDT = Decimal(os.getenv("ELITE_MARKUP_USDT", str(MARKUP_USDT)))
DB = os.getenv("DB_FILE", "ars_bot.db").strip()
PRODUCT_CACHE_SECONDS = max(0, int(os.getenv("PRODUCT_CACHE_SECONDS", "8")))
PRODUCTS_PER_PAGE = max(5, min(40, int(os.getenv("PRODUCTS_PER_PAGE", "20"))))
FIRST_PAGE_PRODUCTS = max(4, min(12, int(os.getenv("FIRST_PAGE_PRODUCTS", "8"))))

# Customer-facing shop settings. Supplier identities stay internal.
SHOP_NAME = os.getenv("SHOP_NAME", "Digital Shop").strip() or "Digital Shop"
SUPPORT_URL = os.getenv("SUPPORT_URL", "").strip()
SUPPORT_USERNAME = os.getenv("SUPPORT_USERNAME", "").strip()
SUPPORT_TEXT = os.getenv(
    "SUPPORT_TEXT",
    "If you need help, contact Support. Please include your order reference when available.",
).strip()
FEATURED_PRODUCT_KEYWORDS = tuple(
    k.strip().casefold()
    for k in os.getenv("FEATURED_PRODUCT_KEYWORDS", "gemini,jio").split(",")
    if k.strip()
)

MAIN_PRODUCT_KEYWORDS = tuple(
    k.strip().casefold()
    for k in os.getenv(
        "MAIN_PRODUCT_KEYWORDS",
        "gemini jio,jio 18,gemini 18m jio,gemini jio 18",
    ).split(",")
    if k.strip()
)

required = {
    "BOT_TOKEN": BOT_TOKEN,
    "PAYMENT_API_KEY": PAYMENT_API_KEY,
    "PAYMENT_WEBHOOK_SECRET": PAYMENT_WEBHOOK_SECRET,
}
missing = [k for k, v in required.items() if not v]
if missing:
    raise RuntimeError("Missing required .env values: " + ", ".join(missing))

TG = f"https://api.telegram.org/bot{BOT_TOKEN}"
AHEAD = {"X-API-Key": API_KEY}
EHEAD = {"X-API-Key": ELITE_API_KEY}
PHEAD = {"X-API-Key": PAYMENT_API_KEY, "Content-Type": "application/json"}
HTTP = requests.Session()

_PAYMENT_OK = {"PAID", "SUCCESS", "COMPLETED", "CONFIRMED"}

# -----------------------------------------------------------------------------
# Small helpers
# -----------------------------------------------------------------------------
def money(value: Any) -> Decimal:
    """Parse money and normalize to 2 decimal places."""
    try:
        return Decimal(str(value)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    except (InvalidOperation, TypeError, ValueError):
        raise ValueError(f"Invalid amount: {value!r}")


def fmoney(value: Any) -> str:
    return f"{money(value):.2f}"


def now_sql() -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S")


def new_ref(prefix: str) -> str:
    return f"{prefix}-{uuid.uuid4().hex[:10].upper()}"


def chunks(items: Iterable[Any], size: int):
    buf = []
    for item in items:
        buf.append(item)
        if len(buf) >= size:
            yield buf
            buf = []
    if buf:
        yield buf


def public_product_name(value: Any) -> str:
    """Return a customer-safe product name without supplier/board branding."""
    name = str(value or "Unknown")
    # Hide only explicit upstream board branding; do not alter the actual offer name.
    name = re.sub(r"(?i)\[\s*(?:AIV|ETS)\s*\]", "", name)
    name = re.sub(r"(?i)\bAIVerse\b", "", name)
    name = re.sub(r"(?i)\bElite\s+Tools(?:\s+Store)?\b", "", name)
    name = re.sub(r"\s{2,}", " ", name).strip(" -|•:[]")
    return name or "Digital Product"


def is_featured_product(x: dict) -> bool:
    name = public_product_name(x.get("name", "")).casefold()
    return any(keyword in name for keyword in FEATURED_PRODUCT_KEYWORDS)


def is_main_product(x: dict) -> bool:
    """Identify the shop's primary Gemini Jio offer."""
    name = public_product_name(x.get("name", "")).casefold()
    return any(keyword in name for keyword in MAIN_PRODUCT_KEYWORDS)


def product_display_priority(x: dict) -> tuple:
    """
    Customer sort order:
      1) in-stock OWN/custom products
      2) in-stock main Gemini/Jio supplier offer
      3) other in-stock Gemini/Jio offers
      4) other in-stock products
      5) out-of-stock OWN/custom products
      6) remaining out-of-stock products
    """
    stock = int(x.get("stock", 0) or 0)
    in_stock = stock > 0
    own = str(x.get("supplier", "")).upper() == "OWN"

    if in_stock and own:
        tier = -1
    elif in_stock and is_main_product(x):
        tier = 0
    elif in_stock and is_featured_product(x):
        tier = 1
    elif in_stock:
        tier = 2
    elif own:
        tier = 3
    elif is_main_product(x):
        tier = 4
    elif is_featured_product(x):
        tier = 5
    else:
        tier = 6

    return (
        tier,
        public_product_name(x.get("name", "")).casefold(),
        str(x.get("product_key", "")),
    )


def customer_catalog(products: list[dict]) -> list[dict]:
    """Hide duplicate same-name listings while preferring available OWN stock."""
    best: dict[str, dict] = {}
    for item in products:
        key = re.sub(r"\s+", " ", public_product_name(item.get("name", "")).casefold()).strip()
        current = best.get(key)
        if current is None:
            best[key] = item
            continue

        cur_stock = int(current.get("stock", 0) or 0) > 0
        new_stock = int(item.get("stock", 0) or 0) > 0
        cur_own = str(current.get("supplier", "")).upper() == "OWN"
        new_own = str(item.get("supplier", "")).upper() == "OWN"

        choose_new = False
        if new_stock != cur_stock:
            choose_new = new_stock
        elif new_stock and new_own != cur_own:
            choose_new = new_own
        elif new_own == cur_own:
            choose_new = customer_price(item) < customer_price(current)

        if choose_new:
            best[key] = item
    return list(best.values())


# -----------------------------------------------------------------------------
# Database + migrations
# -----------------------------------------------------------------------------
def db() -> sqlite3.Connection:
    c = sqlite3.connect(DB, timeout=30)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA foreign_keys=ON")
    c.execute("PRAGMA busy_timeout=30000")
    return c


def _columns(c: sqlite3.Connection, table: str) -> set[str]:
    return {r[1] for r in c.execute(f"PRAGMA table_info({table})").fetchall()}


def _add_column(c: sqlite3.Connection, table: str, definition: str) -> None:
    name = definition.split()[0]
    if name not in _columns(c, table):
        c.execute(f"ALTER TABLE {table} ADD COLUMN {definition}")


def init_db() -> None:
    c = db()
    c.execute("PRAGMA journal_mode=WAL")

    c.execute(
        """CREATE TABLE IF NOT EXISTS users(
            telegram_id TEXT PRIMARY KEY,
            username TEXT,
            first_name TEXT,
            balance REAL DEFAULT 0,
            joined_at TEXT DEFAULT CURRENT_TIMESTAMP,
            last_seen TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS orders(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_ref TEXT UNIQUE,
            telegram_id TEXT,
            service_id TEXT,
            product_name TEXT,
            quantity INTEGER DEFAULT 1,
            supplier_price REAL,
            customer_price REAL,
            status TEXT,
            invoice_id TEXT UNIQUE,
            payment_uid TEXT,
            txid TEXT,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS transactions(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            telegram_id TEXT,
            kind TEXT,
            amount REAL,
            balance_before REAL,
            balance_after REAL,
            reference TEXT UNIQUE,
            status TEXT,
            note TEXT,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS topups(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            topup_ref TEXT UNIQUE,
            telegram_id TEXT,
            amount REAL,
            invoice_id TEXT UNIQUE,
            payment_uid TEXT,
            txid TEXT,
            status TEXT DEFAULT 'PENDING',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS settings(
            key TEXT PRIMARY KEY,
            value TEXT
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS user_states(
            telegram_id TEXT PRIMARY KEY,
            state TEXT,
            payload TEXT,
            updated_at TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS payment_claims(
            payment_id TEXT PRIMARY KEY,
            invoice_id TEXT NOT NULL,
            kind TEXT NOT NULL,
            reference TEXT NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS supplier_catalog(
            product_key TEXT PRIMARY KEY,
            supplier TEXT NOT NULL,
            product_id TEXT NOT NULL,
            name TEXT,
            price REAL,
            stock INTEGER,
            raw_json TEXT,
            updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(supplier, product_id)
        )"""
    )

    c.execute(
        """CREATE TABLE IF NOT EXISTS custom_products(
            product_key TEXT PRIMARY KEY,
            name TEXT NOT NULL,
            price REAL NOT NULL,
            validity TEXT DEFAULT '',
            warranty TEXT DEFAULT 'No Warranty',
            enabled INTEGER DEFAULT 1,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT DEFAULT CURRENT_TIMESTAMP
        )"""
    )
    c.execute(
        """CREATE TABLE IF NOT EXISTS custom_stock(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            product_key TEXT NOT NULL,
            payload TEXT NOT NULL,
            status TEXT DEFAULT 'AVAILABLE',
            order_ref TEXT,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP,
            reserved_at TEXT,
            delivered_at TEXT,
            UNIQUE(product_key, payload),
            FOREIGN KEY(product_key) REFERENCES custom_products(product_key)
        )"""
    )

    # Backward-compatible migrations for databases created by either uploaded bot.
    _add_column(c, "orders", "payment_method TEXT DEFAULT 'BALANCE'")
    _add_column(c, "orders", "delivery_payload TEXT")
    _add_column(c, "orders", "delivery_error TEXT")
    _add_column(c, "orders", "delivery_attempts INTEGER DEFAULT 0")
    _add_column(c, "orders", "paid_at TEXT")
    _add_column(c, "orders", "delivered_at TEXT")
    _add_column(c, "orders", "supplier TEXT DEFAULT 'AIVERSE'")
    _add_column(c, "orders", "product_key TEXT")

    # Existing orders came from the original AIVerse-only build.
    c.execute("UPDATE orders SET supplier='AIVERSE' WHERE supplier IS NULL OR TRIM(supplier)=''")

    # Orders from the older direct-PayHub bot already have invoice_id populated.
    # Mark those as DIRECT when migrating; ARS balance orders normally have no invoice_id.
    c.execute(
        """UPDATE orders SET payment_method='DIRECT'
           WHERE invoice_id IS NOT NULL AND TRIM(invoice_id)<>''
             AND (payment_method IS NULL OR payment_method='BALANCE')"""
    )

    c.execute("CREATE INDEX IF NOT EXISTS idx_orders_user ON orders(telegram_id, id DESC)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_orders_status ON orders(status)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_topups_user ON topups(telegram_id, id DESC)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_topups_status ON topups(status)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_tx_user ON transactions(telegram_id, id DESC)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_orders_supplier ON orders(supplier, service_id)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_catalog_supplier ON supplier_catalog(supplier, product_id)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_custom_stock_product_status ON custom_stock(product_key,status,id)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_custom_stock_order ON custom_stock(order_ref,status)")
    c.commit()
    c.close()


def upsert_user_from_user(u: Dict[str, Any]) -> None:
    uid = u.get("id")
    if uid is None:
        return
    c = db()
    c.execute(
        """INSERT INTO users(telegram_id,username,first_name)
           VALUES(?,?,?)
           ON CONFLICT(telegram_id) DO UPDATE SET
             username=excluded.username,
             first_name=excluded.first_name,
             last_seen=CURRENT_TIMESTAMP""",
        (str(uid), u.get("username") or "", u.get("first_name") or ""),
    )
    c.commit()
    c.close()


def upsert_user(m: Dict[str, Any]) -> None:
    upsert_user_from_user(m.get("from", {}))


def set_state(uid: Any, state: str, payload: Optional[dict] = None) -> None:
    c = db()
    c.execute(
        """INSERT INTO user_states(telegram_id,state,payload,updated_at)
           VALUES(?,?,?,CURRENT_TIMESTAMP)
           ON CONFLICT(telegram_id) DO UPDATE SET
             state=excluded.state,payload=excluded.payload,updated_at=CURRENT_TIMESTAMP""",
        (str(uid), state, json.dumps(payload or {})),
    )
    c.commit()
    c.close()


def get_state(uid: Any) -> Tuple[str, dict]:
    c = db()
    r = c.execute(
        "SELECT state,payload FROM user_states WHERE telegram_id=?", (str(uid),)
    ).fetchone()
    c.close()
    if not r:
        return "", {}
    try:
        payload = json.loads(r["payload"] or "{}")
    except Exception:
        payload = {}
    return r["state"] or "", payload


def clear_state(uid: Any) -> None:
    c = db()
    c.execute("DELETE FROM user_states WHERE telegram_id=?", (str(uid),))
    c.commit()
    c.close()


def get_setting(key: str, default: str = "") -> str:
    c = db()
    r = c.execute("SELECT value FROM settings WHERE key=?", (str(key),)).fetchone()
    c.close()
    return str(r["value"]) if r else str(default)


def set_setting_value(key: str, value: Any) -> None:
    c = db()
    c.execute(
        """INSERT INTO settings(key,value) VALUES(?,?)
           ON CONFLICT(key) DO UPDATE SET value=excluded.value""",
        (str(key), str(value)),
    )
    c.commit()
    c.close()


def supplier_enabled(supplier: str) -> bool:
    supplier = str(supplier or "").upper()
    if supplier not in {"AIVERSE", "ELITE"}:
        return True
    return get_setting(f"supplier_enabled:{supplier}", "1") == "1"


def set_supplier_enabled(supplier: str, enabled: bool) -> None:
    supplier = str(supplier or "").upper()
    if supplier not in {"AIVERSE", "ELITE"}:
        raise ValueError("Unknown supplier")
    set_setting_value(f"supplier_enabled:{supplier}", "1" if enabled else "0")
    # Clear product cache immediately so the shop reflects the new state.
    try:
        with _product_lock:
            if supplier in _product_cache:
                _product_cache[supplier] = {"at": 0.0, "services": []}
    except Exception:
        pass


def _custom_product_row(product_key: str) -> Optional[sqlite3.Row]:
    c = db()
    r = c.execute(
        "SELECT * FROM custom_products WHERE product_key=?",
        (str(product_key),),
    ).fetchone()
    c.close()
    return r


def _custom_stock_counts(product_key: str) -> dict:
    c = db()
    rows = c.execute(
        """SELECT status,COUNT(*) n FROM custom_stock
           WHERE product_key=? GROUP BY status""",
        (str(product_key),),
    ).fetchall()
    c.close()
    out = {"AVAILABLE": 0, "RESERVED": 0, "DELIVERED": 0}
    for r in rows:
        out[str(r["status"]).upper()] = int(r["n"])
    return out


def own_services(include_disabled: bool = False) -> list[dict]:
    c = db()
    where = "" if include_disabled else "WHERE p.enabled=1"
    rows = c.execute(
        f"""SELECT p.*,
              COALESCE(SUM(CASE WHEN s.status='AVAILABLE' THEN 1 ELSE 0 END),0) AS available_stock
            FROM custom_products p
            LEFT JOIN custom_stock s ON s.product_key=p.product_key
            {where}
            GROUP BY p.product_key
            ORDER BY p.id""".replace("p.id", "p.created_at")
    ).fetchall()
    c.close()
    out = []
    for r in rows:
        key = str(r["product_key"])
        out.append(
            {
                "supplier": "OWN",
                "product_id": key,
                "service_id": key,
                "product_key": key,
                "name": str(r["name"]),
                # For OWN products price is already the final customer price.
                "price": money(r["price"]),
                "stock": int(r["available_stock"] or 0),
                "raw": {
                    "validity": str(r["validity"] or ""),
                    "warranty": str(r["warranty"] or "No Warranty"),
                    "own_stock": True,
                },
            }
        )
    return out


def own_service(product_key: str, include_disabled: bool = False) -> Optional[dict]:
    row = _custom_product_row(product_key)
    if not row:
        return None
    if not include_disabled and not int(row["enabled"] or 0):
        return None
    counts = _custom_stock_counts(product_key)
    return {
        "supplier": "OWN",
        "product_id": str(row["product_key"]),
        "service_id": str(row["product_key"]),
        "product_key": str(row["product_key"]),
        "name": str(row["name"]),
        "price": money(row["price"]),
        "stock": int(counts.get("AVAILABLE", 0)),
        "raw": {
            "validity": str(row["validity"] or ""),
            "warranty": str(row["warranty"] or "No Warranty"),
            "own_stock": True,
        },
    }


def create_custom_product(name: str, price: Any, validity: str, warranty: str) -> str:
    key = "OWN-" + uuid.uuid4().hex[:10].upper()
    c = db()
    c.execute(
        """INSERT INTO custom_products(product_key,name,price,validity,warranty,enabled)
           VALUES(?,?,?,?,?,1)""",
        (
            key,
            str(name).strip(),
            float(money(price)),
            str(validity).strip(),
            str(warranty).strip() or "No Warranty",
        ),
    )
    c.commit()
    c.close()
    return key


def add_custom_stock(product_key: str, payloads: list[str]) -> tuple[int, int]:
    clean = []
    seen = set()
    for item in payloads:
        value = str(item).strip()
        if not value or value in seen:
            continue
        clean.append(value)
        seen.add(value)
    added = skipped = 0
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        for payload in clean:
            try:
                c.execute(
                    """INSERT INTO custom_stock(product_key,payload,status)
                       VALUES(?,?,'AVAILABLE')""",
                    (str(product_key), payload),
                )
                added += 1
            except sqlite3.IntegrityError:
                skipped += 1
        c.commit()
    finally:
        c.close()
    return added, skipped


def _reserve_own_stock_tx(
    c: sqlite3.Connection,
    product_key: str,
    quantity: int,
    order_ref: str,
) -> None:
    rows = c.execute(
        """SELECT id FROM custom_stock
           WHERE product_key=? AND status='AVAILABLE'
           ORDER BY id LIMIT ?""",
        (str(product_key), int(quantity)),
    ).fetchall()
    if len(rows) != int(quantity):
        raise ValueError("OUT_OF_STOCK")
    ids = [int(r["id"]) for r in rows]
    marks = ",".join("?" for _ in ids)
    params = [str(order_ref), *ids]
    c.execute(
        f"""UPDATE custom_stock
            SET status='RESERVED',order_ref=?,reserved_at=CURRENT_TIMESTAMP
            WHERE id IN ({marks}) AND status='AVAILABLE'""",
        params,
    )
    if c.total_changes < len(ids):
        raise ValueError("OUT_OF_STOCK")


def release_own_stock(order_ref: str) -> None:
    c = db()
    c.execute(
        """UPDATE custom_stock
           SET status='AVAILABLE',order_ref=NULL,reserved_at=NULL
           WHERE order_ref=? AND status='RESERVED'""",
        (str(order_ref),),
    )
    c.commit()
    c.close()


def finish_own_stock_delivery(order_ref: str, quantity: int) -> list[str]:
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        rows = c.execute(
            """SELECT id,payload FROM custom_stock
               WHERE order_ref=? AND status='RESERVED'
               ORDER BY id LIMIT ?""",
            (str(order_ref), int(quantity)),
        ).fetchall()
        if len(rows) != int(quantity):
            c.rollback()
            raise SupplierRejected("Reserved own stock is incomplete")
        ids = [int(r["id"]) for r in rows]
        payloads = [str(r["payload"]) for r in rows]
        marks = ",".join("?" for _ in ids)
        c.execute(
            f"""UPDATE custom_stock
                SET status='DELIVERED',delivered_at=CURRENT_TIMESTAMP
                WHERE id IN ({marks}) AND status='RESERVED'""",
            ids,
        )
        c.execute(
            """UPDATE orders SET status='COMPLETED',delivery_payload=?,
               delivery_error=NULL,delivered_at=CURRENT_TIMESTAMP,
               updated_at=CURRENT_TIMESTAMP WHERE order_ref=?""",
            (json.dumps(payloads, ensure_ascii=False), str(order_ref)),
        )
        c.commit()
        return payloads
    finally:
        c.close()


# -----------------------------------------------------------------------------
# Telegram
# -----------------------------------------------------------------------------
def tg(method: str, data: Optional[dict] = None) -> dict:
    r = HTTP.post(f"{TG}/{method}", json=data or {}, timeout=30)
    r.raise_for_status()
    d = r.json()
    if not d.get("ok"):
        raise RuntimeError(d.get("description", "Telegram API error"))
    return d


def send(cid: Any, text: str, kb: Optional[list] = None, parse_mode: Optional[str] = None):
    d: Dict[str, Any] = {"chat_id": cid, "text": text}
    if kb is not None:
        d["reply_markup"] = {"inline_keyboard": kb}
    if parse_mode:
        d["parse_mode"] = parse_mode
    return tg("sendMessage", d)


def answer(qid: str, text: str = "") -> None:
    try:
        tg("answerCallbackQuery", {"callback_query_id": qid, "text": text})
    except Exception:
        pass


def public_log(title: str, body: str) -> None:
    """
    Internal event logger.

    V8 privacy rule:
    The Telegram LOG_CHAT_ID group is NOT used for generic bot/admin/error events.
    Only group_topup_log() and group_purchase_log() may publish customer activity.
    """
    print(f"[EVENT] {title} | {body.replace(chr(10), ' | ')}")


def group_topup_log(amount: Any) -> None:
    """Publish an anonymous successful Add Funds event to the activity group."""
    if not LOG_CHAT_ID:
        return
    try:
        send(
            LOG_CHAT_ID,
            "💎 Funds Added\n\n"
            "👤 Customer: Hidden\n"
            f"💰 Amount: {fmoney(amount)} USDT\n"
            "✅ Status: Successful",
        )
    except Exception as e:
        print("Group topup log error:", e)


def group_purchase_log(product_name: str, quantity: Any, amount: Any) -> None:
    """Publish an anonymous completed purchase to the activity group."""
    if not LOG_CHAT_ID:
        return
    try:
        qty = max(1, int(quantity or 1))
    except Exception:
        qty = 1
    try:
        send(
            LOG_CHAT_ID,
            "🛒 Purchase Completed\n\n"
            "👤 Customer: Hidden\n"
            f"📦 Product: {public_product_name(product_name)}\n"
            f"🔢 Quantity: {qty}\n"
            f"💵 Amount: {fmoney(amount)} USDT\n"
            "✅ Status: Completed",
        )
    except Exception as e:
        print("Group purchase log error:", e)


def configure_telegram_ui() -> None:
    """Show bot commands in private chats only; groups get no slash-command menu."""
    commands = [
        {"command": "start", "description": "Start / open main menu"},
        {"command": "menu", "description": "Open main menu"},
        {"command": "shop", "description": "Browse and purchase products"},
        {"command": "topup", "description": "Add balance"},
        {"command": "wallet", "description": "Wallet, balance and transactions"},
        {"command": "orders", "description": "My orders"},
        {"command": "support", "description": "Contact support"},
    ]
    admin_commands = commands + [
        {"command": "admin", "description": "Open admin control panel"},
    ]

    try:
        # Remove old global/group command scopes left by previous versions.
        try:
            tg("deleteMyCommands", {})
        except Exception:
            pass
        try:
            tg("deleteMyCommands", {"scope": {"type": "all_group_chats"}})
        except Exception:
            pass

        # Customer slash commands only in private bot chats.
        tg(
            "setMyCommands",
            {
                "commands": commands,
                "scope": {"type": "all_private_chats"},
            },
        )

        # The Telegram Menu button applies to bot private chats.
        tg("setChatMenuButton", {"menu_button": {"type": "commands"}})

        # Admin gets /admin only in the admin's private chat.
        for admin_id in ADMIN_IDS:
            try:
                tg(
                    "setMyCommands",
                    {
                        "commands": admin_commands,
                        "scope": {"type": "chat", "chat_id": int(admin_id)},
                    },
                )
            except Exception as e:
                print("Admin command scope warning:", admin_id, e)

        print("✅ Private-chat commands configured; group command menu disabled")
    except Exception as e:
        print("Telegram menu setup warning:", e)


# -----------------------------------------------------------------------------
# Membership gate
# -----------------------------------------------------------------------------
def member_ok(chat: str, user_id: Any) -> bool:
    if not chat:
        return True
    try:
        d = tg("getChatMember", {"chat_id": chat, "user_id": int(user_id)}).get(
            "result", {}
        )
        st = d.get("status")
        return st in ("creator", "administrator", "member") or (
            st == "restricted" and d.get("is_member") is True
        )
    except Exception as e:
        print("Membership check:", chat, e)
        return False


def joined(uid: Any) -> bool:
    return member_ok(FORCE_CHANNEL, uid) and member_ok(FORCE_GROUP, uid)


def join_gate(cid: Any) -> None:
    kb = []
    if FORCE_CHANNEL_URL:
        kb.append([{"text": "📢 Join Channel", "url": FORCE_CHANNEL_URL}])
    if FORCE_GROUP_URL:
        kb.append([{"text": "👥 Join Group", "url": FORCE_GROUP_URL}])
    kb.append([{"text": "✅ Verify Membership", "callback_data": "verify_join"}])
    send(
        cid,
        "🔐 To use the bot, please join the required Channel and Group first.\n\n"
        "After joining both, tap Verify Membership below.",
        kb,
    )


# -----------------------------------------------------------------------------
# Supplier APIs: AIVerse + Elite Tools Store
# -----------------------------------------------------------------------------
_product_cache: Dict[str, Dict[str, Any]] = {
    "AIVERSE": {"at": 0.0, "services": []},
    "ELITE": {"at": 0.0, "services": []},
}
_product_lock = threading.Lock()


class SupplierRejected(RuntimeError):
    """Supplier explicitly rejected the order; safe to treat as not delivered."""


class SupplierAmbiguous(RuntimeError):
    """Supplier outcome is uncertain; do not retry/refund automatically."""


def _first(d: dict, *keys: str, default: Any = None) -> Any:
    for key in keys:
        if key in d and d.get(key) is not None:
            return d.get(key)
    return default


def _to_stock(value: Any, raw: Optional[dict] = None) -> int:
    if isinstance(value, bool):
        return 1 if value else 0
    try:
        return max(0, int(float(value)))
    except Exception:
        pass
    if raw:
        active = _first(raw, "active", "enabled", "available", "inStock", "in_stock")
        if isinstance(active, bool):
            return 999999 if active else 0
        status = str(_first(raw, "status", default="")).upper()
        if status in {"ACTIVE", "AVAILABLE", "IN_STOCK", "INSTOCK"}:
            return 999999
        if status in {"INACTIVE", "OUT_OF_STOCK", "OUT", "SOLD_OUT", "DISABLED"}:
            return 0
    # Some reseller APIs do not expose a numeric stock field. A listed product is
    # treated as available and the supplier remains authoritative at checkout.
    return 999999


def _normalize_product(raw: dict, supplier: str) -> Optional[dict]:
    if not isinstance(raw, dict):
        return None
    supplier = supplier.upper()
    if supplier == "AIVERSE":
        pid = _first(raw, "service_id", "productId", "product_id", "id")
        name = _first(raw, "name", "title", "productName", "product_name", default="Unknown")
        price = _first(raw, "price", "resellerPrice", "reseller_price", "unitPrice", "unit_price")
        stock_raw = _first(raw, "stock", "quantity", "availableStock", "available_stock")
    else:
        pid = _first(raw, "productId", "product_id", "id", "service_id", "_id")
        name = _first(raw, "name", "title", "productName", "product_name", default="Unknown")
        price = _first(
            raw,
            "price",
            "resellerPrice",
            "reseller_price",
            "unitPrice",
            "unit_price",
            "salePrice",
            "sale_price",
        )
        stock_raw = _first(raw, "stock", "quantity", "availableStock", "available_stock", "qty")
    if pid is None or price is None:
        return None
    try:
        p = money(price)
    except Exception:
        return None
    return {
        "supplier": supplier,
        "product_id": str(pid),
        "service_id": str(pid),  # compatibility with original ARS DB/schema
        "name": str(name),
        "price": p,
        "stock": _to_stock(stock_raw, raw),
        "raw": raw,
    }


def _extract_product_list(data: Any) -> list:
    if isinstance(data, list):
        return data
    if not isinstance(data, dict):
        return []
    for key in ("services", "products", "items", "data", "result"):
        v = data.get(key)
        if isinstance(v, list):
            return v
        if isinstance(v, dict):
            for nested in ("services", "products", "items"):
                if isinstance(v.get(nested), list):
                    return v[nested]
    return []


def _supplier_get_json(urls: list[str], headers: dict, label: str) -> dict:
    last_error: Optional[Exception] = None
    for i, url in enumerate(urls):
        try:
            r = HTTP.get(url, headers=headers, timeout=20)
        except requests.RequestException as e:
            last_error = e
            continue
        if r.status_code == 404 and i + 1 < len(urls):
            continue
        try:
            d = r.json()
        except Exception as e:
            raise RuntimeError(f"{label} returned non-JSON HTTP {r.status_code}") from e
        if r.status_code >= 400:
            if isinstance(d, dict):
                msg = d.get("message") or d.get("error")
            else:
                msg = None
            raise RuntimeError(msg or f"{label} HTTP {r.status_code}")
        return d
    raise RuntimeError(f"{label} unavailable: {last_error or 'no working endpoint'}")


def _catalog_key(supplier: str, product_id: str) -> str:
    return hashlib.sha256(f"{supplier.upper()}|{product_id}".encode()).hexdigest()[:16]


def _save_catalog(products: list[dict]) -> None:
    if not products:
        return
    c = db()
    for x in products:
        key = _catalog_key(x["supplier"], x["product_id"])
        x["product_key"] = key
        try:
            raw_json = json.dumps(x.get("raw") or {}, ensure_ascii=False)
        except Exception:
            raw_json = "{}"
        c.execute(
            """INSERT INTO supplier_catalog(product_key,supplier,product_id,name,price,stock,raw_json,updated_at)
               VALUES(?,?,?,?,?,?,?,CURRENT_TIMESTAMP)
               ON CONFLICT(supplier,product_id) DO UPDATE SET
                 product_key=excluded.product_key,name=excluded.name,price=excluded.price,
                 stock=excluded.stock,raw_json=excluded.raw_json,updated_at=CURRENT_TIMESTAMP""",
            (
                key,
                x["supplier"],
                x["product_id"],
                x["name"],
                float(x["price"]),
                int(x["stock"]),
                raw_json,
            ),
        )
    c.commit()
    c.close()


def aiverse_services(force: bool = False) -> list:
    supplier = "AIVERSE"
    now = time.time()
    with _product_lock:
        cache = _product_cache[supplier]
        if not force and cache["services"] and now - float(cache["at"]) <= PRODUCT_CACHE_SECONDS:
            return [dict(x) for x in cache["services"]]
    d = _supplier_get_json([f"{BASE_URL}/api/v1/products"], AHEAD, "AIVerse products")
    out = []
    for raw in _extract_product_list(d):
        x = _normalize_product(raw, supplier)
        if x:
            out.append(x)
    _save_catalog(out)
    with _product_lock:
        _product_cache[supplier] = {"at": now, "services": out}
    return [dict(x) for x in out]


def elite_services(force: bool = False) -> list:
    supplier = "ELITE"
    now = time.time()
    with _product_lock:
        cache = _product_cache[supplier]
        if not force and cache["services"] and now - float(cache["at"]) <= PRODUCT_CACHE_SECONDS:
            return [dict(x) for x in cache["services"]]
    # The current public route advertises /api/reseller/products. /api/products is
    # retained only as a compatibility fallback for older deployments.
    urls = [f"{ELITE_BASE_URL}{ELITE_PRODUCTS_PATH}"]
    if ELITE_PRODUCTS_PATH != "/api/products":
        urls.append(f"{ELITE_BASE_URL}/api/products")
    d = _supplier_get_json(urls, EHEAD, "Elite products")
    out = []
    for raw in _extract_product_list(d):
        x = _normalize_product(raw, supplier)
        if x:
            out.append(x)
    _save_catalog(out)
    with _product_lock:
        _product_cache[supplier] = {"at": now, "services": out}
    return [dict(x) for x in out]


def supplier_services(supplier: str, force: bool = False) -> list:
    supplier = supplier.upper()
    if supplier == "AIVERSE":
        return aiverse_services(force=force)
    if supplier == "ELITE":
        return elite_services(force=force)
    raise RuntimeError(f"Unknown supplier: {supplier}")


def services(force: bool = False) -> list:
    """
    Return only enabled upstream suppliers plus enabled OWN products.
    Supplier toggles affect NEW catalog/checkout only; already-paid orders remain locked
    to their original supplier and continue through the delivery state machine.
    """
    all_products: list[dict] = []
    errors: list[str] = []

    for supplier in ("AIVERSE", "ELITE"):
        if not supplier_enabled(supplier):
            continue
        try:
            all_products.extend(supplier_services(supplier, force=force))
        except Exception as e:
            errors.append(f"{supplier}: {e}")
            print(f"{supplier} product load error:", e)

    try:
        all_products.extend(own_services())
    except Exception as e:
        errors.append(f"OWN: {e}")
        print("OWN product load error:", e)

    if not all_products and errors:
        raise RuntimeError(" | ".join(errors))
    return all_products


def _catalog_lookup(token: str) -> Optional[sqlite3.Row]:
    c = db()
    r = c.execute(
        "SELECT * FROM supplier_catalog WHERE product_key=?", (str(token),)
    ).fetchone()
    c.close()
    return r


def service(token: str, force: bool = False) -> Optional[dict]:
    """Resolve an OWN product or an enabled upstream catalog product."""
    token = str(token)

    own = own_service(token)
    if own:
        return own

    cat = _catalog_lookup(token)
    if cat:
        supplier = str(cat["supplier"] or "").upper()
        # Supplier OFF blocks new browsing/checkout from old buttons too.
        if not supplier_enabled(supplier):
            return None
        try:
            ss = supplier_services(supplier, force=force)
            x = next((p for p in ss if str(p["product_id"]) == str(cat["product_id"])), None)
            if x:
                x["product_key"] = cat["product_key"]
                return x
        except Exception:
            if force:
                raise

        # Display fallback is allowed only while supplier remains enabled.
        try:
            raw = json.loads(cat["raw_json"] or "{}")
        except Exception:
            raw = {}
        return {
            "supplier": supplier,
            "product_id": cat["product_id"],
            "service_id": cat["product_id"],
            "product_key": cat["product_key"],
            "name": cat["name"] or "Unknown",
            "price": money(cat["price"] or 0),
            "stock": int(cat["stock"] or 0),
            "raw": raw,
        }

    # Backward compatibility with very old AIVerse callbacks, but only if enabled.
    if supplier_enabled("AIVERSE"):
        ss = aiverse_services(force=force)
        x = next((p for p in ss if str(p["product_id"]) == token), None)
        if x:
            x["product_key"] = _catalog_key("AIVERSE", x["product_id"])
        return x
    return None


def customer_price(x: dict) -> Decimal:
    supplier = str(x.get("supplier", "AIVERSE")).upper()
    if supplier == "OWN":
        return money(x.get("price", 0))
    markup = ELITE_MARKUP_USDT if supplier == "ELITE" else AIVERSE_MARKUP_USDT
    return money(money(x.get("price", 0)) + markup)


def aiverse_order(product_id: str, quantity: int = 1) -> dict:
    try:
        r = HTTP.post(
            f"{BASE_URL}/api/v1/order",
            headers={**AHEAD, "Content-Type": "application/json"},
            json={"service_id": product_id, "quantity": max(1, int(quantity))},
            timeout=30,
        )
    except (requests.Timeout, requests.ConnectionError) as e:
        raise SupplierAmbiguous(f"Network error after AIVerse order request: {e}") from e
    except requests.RequestException as e:
        raise SupplierAmbiguous(f"AIVerse request error: {e}") from e
    try:
        d = r.json()
    except Exception as e:
        raise SupplierAmbiguous(f"AIVerse returned non-JSON HTTP {r.status_code}; outcome uncertain") from e
    if 400 <= r.status_code < 500:
        raise SupplierRejected(d.get("error") or d.get("message") or f"AIVerse HTTP {r.status_code}")
    if r.status_code >= 500:
        raise SupplierAmbiguous(d.get("error") or d.get("message") or f"AIVerse HTTP {r.status_code}")
    if d.get("success") is False or ("success" in d and not d.get("success")):
        raise SupplierRejected(d.get("error") or d.get("message") or "AIVerse rejected order")
    return d


def elite_order(product_id: str, quantity: int = 1) -> dict:
    urls = [f"{ELITE_BASE_URL}{ELITE_ORDER_PATH}"]
    if ELITE_ORDER_PATH != "/api/order":
        urls.append(f"{ELITE_BASE_URL}/api/order")
    last_404 = None
    for i, url in enumerate(urls):
        try:
            r = HTTP.post(
                url,
                headers={**EHEAD, "Content-Type": "application/json"},
                json={"productId": product_id, "quantity": max(1, int(quantity))},
                timeout=30,
            )
        except (requests.Timeout, requests.ConnectionError) as e:
            raise SupplierAmbiguous(f"Network error after Elite order request: {e}") from e
        except requests.RequestException as e:
            raise SupplierAmbiguous(f"Elite request error: {e}") from e
        try:
            d = r.json()
        except Exception as e:
            raise SupplierAmbiguous(f"Elite returned non-JSON HTTP {r.status_code}; outcome uncertain") from e
        # Route-not-found can safely use the documented compatibility fallback because
        # no order was accepted by that endpoint.
        if r.status_code == 404 and i + 1 < len(urls):
            last_404 = d
            continue
        if 400 <= r.status_code < 500:
            msg = (d.get("error") or d.get("message")) if isinstance(d, dict) else None
            raise SupplierRejected(msg or f"Elite HTTP {r.status_code}")
        if r.status_code >= 500:
            msg = (d.get("error") or d.get("message")) if isinstance(d, dict) else None
            raise SupplierAmbiguous(msg or f"Elite HTTP {r.status_code}")
        if isinstance(d, list):
            return {"data": d}
        if not isinstance(d, dict):
            raise SupplierAmbiguous("Elite returned an unsupported response shape")
        if d.get("ok") is False or d.get("success") is False:
            raise SupplierRejected(d.get("error") or d.get("message") or "Elite rejected order")
        return d
    raise SupplierRejected((last_404 or {}).get("message") or "Elite order endpoint not found")


def supplier_order(supplier: str, product_id: str, quantity: int = 1) -> dict:
    supplier = (supplier or "AIVERSE").upper()
    quantity = max(1, int(quantity))
    if supplier == "AIVERSE":
        return aiverse_order(product_id, quantity)
    if supplier == "ELITE":
        return elite_order(product_id, quantity)
    raise SupplierRejected(f"Unknown supplier: {supplier}")


def _format_delivery_object(obj: dict) -> str:
    preferred = [
        "email", "username", "user", "account", "password", "pass",
        "code", "key", "license", "link", "url", "token"
    ]
    bits = []
    for k in preferred:
        if k in obj and obj[k] not in (None, "", [], {}):
            bits.append(f"{k}: {obj[k]}")
    if bits:
        return " | ".join(bits)
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))


def _flatten_delivery(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value] if value.strip() else []
    if isinstance(value, (int, float)):
        return [str(value)]
    if isinstance(value, list):
        out: list[str] = []
        for item in value:
            if isinstance(item, dict):
                out.append(_format_delivery_object(item))
            else:
                out.extend(_flatten_delivery(item))
        return [x for x in out if x.strip()]
    if isinstance(value, dict):
        return [_format_delivery_object(value)]
    return [str(value)]


def extract_delivery_payload(data: dict, supplier: str) -> list[str]:
    """Extract instant accounts/codes/links from either supplier's response."""
    if not isinstance(data, dict):
        return []
    keys = (
        "products", "product", "accounts", "account", "deliveredAccounts", "delivered_accounts",
        "codes", "code", "delivered", "delivery", "deliveryData", "delivery_data",
        "credentials", "credentialsList", "items", "licenses", "keys", "link", "url"
    )
    for key in keys:
        if key in data and data.get(key) not in (None, "", [], {}):
            out = _flatten_delivery(data.get(key))
            if out:
                return out
    nested = data.get("data") or data.get("result")
    if isinstance(nested, dict):
        for key in keys:
            if key in nested and nested.get(key) not in (None, "", [], {}):
                out = _flatten_delivery(nested.get(key))
                if out:
                    return out
    if isinstance(nested, list):
        return _flatten_delivery(nested)
    return []


def elite_balance() -> dict:
    urls = [f"{ELITE_BASE_URL}{ELITE_BALANCE_PATH}"]
    if ELITE_BALANCE_PATH != "/api/balance":
        urls.append(f"{ELITE_BASE_URL}/api/balance")
    return _supplier_get_json(urls, EHEAD, "Elite balance")


# -----------------------------------------------------------------------------
# PayHub API
# -----------------------------------------------------------------------------
def invoice(cid: Any, amount: Decimal) -> Tuple[str, str]:
    r = HTTP.post(
        f"{PAYMENT_BASE_URL}/api/v1/invoice",
        headers=PHEAD,
        json={"telegram_id": str(cid), "amount": fmoney(amount), "currency": "USDT"},
        timeout=30,
    )
    try:
        d = r.json()
    except Exception:
        d = {}
    if r.status_code >= 400 or not d.get("ok"):
        raise RuntimeError(
            d.get("message") or d.get("error") or f"PayHub HTTP {r.status_code}"
        )
    iid = d.get("invoice_id") or d.get("invoiceId") or d.get("invoice_no")
    uid = (
        d.get("uid")
        or d.get("binance_uid")
        or d.get("binanceUid")
        or d.get("pay_uid")
        or d.get("payment_uid")
        or d.get("wallet_id")
        or d.get("walletId")
    )
    if not iid:
        raise RuntimeError("PayHub did not return invoice_id")
    return str(iid), str(uid) if uid else ""


def verify_payhub(iid: str, pid: str) -> Tuple[bool, dict]:
    last: dict = {}
    for key in ("order_id", "txid", "tx_id"):
        try:
            r = HTTP.post(
                f"{PAYMENT_BASE_URL}/api/v1/verify",
                headers=PHEAD,
                json={"invoice_id": str(iid), key: str(pid)},
                timeout=30,
            )
        except requests.RequestException as e:
            last = {"error": str(e)}
            continue
        try:
            d = r.json()
        except Exception:
            d = {}
        last = d
        st = str(d.get("status", "")).upper()
        if (
            d.get("paid") is True
            or d.get("verified") is True
            or d.get("confirmed") is True
            or st in _PAYMENT_OK
        ):
            return True, d
    return False, last


def _payment_amount_currency(data: dict) -> Tuple[Optional[Decimal], str]:
    raw = data.get("amount")
    amt = None
    if raw is not None:
        try:
            amt = money(raw)
        except ValueError:
            amt = None
    currency = str(data.get("currency", "USDT") or "USDT").upper()
    return amt, currency


def _validate_payment(data: dict, expected: Decimal) -> Tuple[bool, str]:
    amt, currency = _payment_amount_currency(data)
    if currency != "USDT":
        return False, "currency-mismatch"
    if amt is not None and amt != money(expected):
        return False, "amount-mismatch"
    return True, "ok"


def _claim_payment(
    c: sqlite3.Connection, payment_id: str, invoice_id: str, kind: str, reference: str
) -> bool:
    """Claim provider payment id globally. Same payment cannot fund two records."""
    pid = (payment_id or f"INVOICE:{invoice_id}").strip()
    try:
        c.execute(
            "INSERT INTO payment_claims(payment_id,invoice_id,kind,reference) VALUES(?,?,?,?)",
            (pid, str(invoice_id), kind, reference),
        )
        return True
    except sqlite3.IntegrityError:
        r = c.execute(
            "SELECT invoice_id,kind,reference FROM payment_claims WHERE payment_id=?", (pid,)
        ).fetchone()
        return bool(
            r
            and str(r["invoice_id"]) == str(invoice_id)
            and r["kind"] == kind
            and r["reference"] == reference
        )


# -----------------------------------------------------------------------------
# Balance / payment accounting
# -----------------------------------------------------------------------------
def get_balance(uid: Any) -> Decimal:
    c = db()
    r = c.execute("SELECT balance FROM users WHERE telegram_id=?", (str(uid),)).fetchone()
    c.close()
    return money(r["balance"] if r else 0)


def _topup_paid_once(topup_ref: str, payment_id: str, data: dict) -> Tuple[str, Optional[Decimal]]:
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT * FROM topups WHERE topup_ref=?", (topup_ref,)).fetchone()
        if not row:
            c.rollback()
            return "not-found", None
        if row["status"] == "PAID":
            bal = c.execute(
                "SELECT balance FROM users WHERE telegram_id=?", (row["telegram_id"],)
            ).fetchone()
            c.commit()
            return "duplicate", money(bal["balance"] if bal else 0)
        if row["status"] != "PENDING":
            c.rollback()
            return "invalid-status", None

        valid, why = _validate_payment(data, money(row["amount"]))
        if not valid:
            c.rollback()
            return why, None

        if not _claim_payment(
            c, payment_id, row["invoice_id"], "TOPUP", row["topup_ref"]
        ):
            c.rollback()
            return "payment-already-used", None

        u = c.execute(
            "SELECT balance FROM users WHERE telegram_id=?", (row["telegram_id"],)
        ).fetchone()
        if not u:
            c.rollback()
            return "user-not-found", None

        before = money(u["balance"])
        amount = money(row["amount"])
        after = money(before + amount)
        c.execute(
            "UPDATE users SET balance=? WHERE telegram_id=?",
            (float(after), row["telegram_id"]),
        )
        c.execute(
            """INSERT INTO transactions(
                 telegram_id,kind,amount,balance_before,balance_after,reference,status,note
               ) VALUES(?,?,?,?,?,?,?,?)""",
            (
                row["telegram_id"],
                "TOPUP",
                float(amount),
                float(before),
                float(after),
                row["topup_ref"],
                "COMPLETED",
                f"Invoice {row['invoice_id']}",
            ),
        )
        c.execute(
            """UPDATE topups SET txid=?,status='PAID',updated_at=CURRENT_TIMESTAMP
               WHERE topup_ref=?""",
            (payment_id, row["topup_ref"]),
        )
        c.commit()
        return "ok", after
    except sqlite3.IntegrityError:
        c.rollback()
        # A unique transaction reference means another worker already completed it.
        return "duplicate", get_balance(row["telegram_id"]) if "row" in locals() and row else None
    finally:
        c.close()


def _mark_direct_paid_once(order_ref: str, payment_id: str, data: dict) -> str:
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT * FROM orders WHERE order_ref=?", (order_ref,)).fetchone()
        if not row:
            c.rollback()
            return "not-found"
        if row["payment_method"] != "DIRECT":
            c.rollback()
            return "not-direct"
        if row["status"] in {
            "PAID",
            "DELIVERING",
            "COMPLETED",
            "DELIVERY_REVIEW",
            "DELIVERY_FAILED",
        }:
            c.commit()
            return "duplicate"
        if row["status"] != "PENDING_PAYMENT":
            c.rollback()
            return "invalid-status"

        valid, why = _validate_payment(data, money(row["customer_price"]))
        if not valid:
            c.rollback()
            return why

        if not _claim_payment(c, payment_id, row["invoice_id"], "ORDER", row["order_ref"]):
            c.rollback()
            return "payment-already-used"

        c.execute(
            """UPDATE orders SET txid=?,status='PAID',paid_at=CURRENT_TIMESTAMP,
               updated_at=CURRENT_TIMESTAMP WHERE order_ref=?""",
            (payment_id, order_ref),
        )
        c.commit()
        return "ok"
    finally:
        c.close()


def create_balance_order(cid: Any, x: dict, quantity: int = 1) -> Tuple[str, Decimal, Decimal]:
    sid = str(x.get("product_id") or x.get("service_id"))
    supplier = str(x.get("supplier", "AIVERSE")).upper()
    product_key = str(x.get("product_key") or (_catalog_key(supplier, sid) if supplier != "OWN" else sid))
    name = str(x.get("name", "Unknown"))
    quantity = _safe_qty(x, quantity)

    cp_unit = customer_price(x)
    cp = money(cp_unit * quantity)
    sp_unit = Decimal("0.00") if supplier == "OWN" else money(x.get("price", 0))
    sp = money(sp_unit * quantity)
    ref = new_ref("ORD")

    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        u = c.execute("SELECT balance FROM users WHERE telegram_id=?", (str(cid),)).fetchone()
        if not u:
            raise RuntimeError("User not found")
        before = money(u["balance"])
        if before < cp:
            c.rollback()
            raise ValueError("INSUFFICIENT_BALANCE")

        # OWN inventory is reserved inside the SAME transaction as balance/order creation.
        # This prevents double-selling one link/code to two customers.
        if supplier == "OWN":
            _reserve_own_stock_tx(c, product_key, quantity, ref)

        after = money(before - cp)
        c.execute("UPDATE users SET balance=? WHERE telegram_id=?", (float(after), str(cid)))
        c.execute(
            """INSERT INTO transactions(
                 telegram_id,kind,amount,balance_before,balance_after,reference,status,note
               ) VALUES(?,?,?,?,?,?,?,?)""",
            (
                str(cid),
                "PURCHASE",
                -float(cp),
                float(before),
                float(after),
                ref,
                "COMPLETED",
                name,
            ),
        )
        c.execute(
            """INSERT INTO orders(
                 order_ref,telegram_id,service_id,product_name,quantity,
                 supplier_price,customer_price,status,payment_method,paid_at,supplier,product_key
               ) VALUES(?,?,?,?,?,?,?,?,?,CURRENT_TIMESTAMP,?,?)""",
            (
                ref, str(cid), sid, name, quantity,
                float(sp), float(cp), "PAID", "BALANCE", supplier, product_key
            ),
        )
        c.commit()
        return ref, cp, after
    except Exception:
        c.rollback()
        raise
    finally:
        c.close()


def refund_balance_order_once(order_ref: str, note: str) -> Tuple[str, Optional[Decimal]]:
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT * FROM orders WHERE order_ref=?", (order_ref,)).fetchone()
        if not row:
            c.rollback()
            return "not-found", None
        if row["payment_method"] != "BALANCE":
            c.rollback()
            return "not-balance", None
        if row["status"] == "REFUNDED":
            bal = c.execute(
                "SELECT balance FROM users WHERE telegram_id=?", (row["telegram_id"],)
            ).fetchone()
            c.commit()
            return "duplicate", money(bal["balance"] if bal else 0)
        if row["status"] not in {"DELIVERING", "DELIVERY_FAILED"}:
            c.rollback()
            return "invalid-status", None

        ref = "REF-" + row["order_ref"]
        existing = c.execute(
            "SELECT 1 FROM transactions WHERE reference=?", (ref,)
        ).fetchone()
        if existing:
            c.execute(
                "UPDATE orders SET status='REFUNDED',updated_at=CURRENT_TIMESTAMP WHERE order_ref=?",
                (order_ref,),
            )
            c.commit()
            return "duplicate", get_balance(row["telegram_id"])

        u = c.execute(
            "SELECT balance FROM users WHERE telegram_id=?", (row["telegram_id"],)
        ).fetchone()
        before = money(u["balance"] if u else 0)
        amount = money(row["customer_price"])
        after = money(before + amount)
        c.execute(
            "UPDATE users SET balance=? WHERE telegram_id=?",
            (float(after), row["telegram_id"]),
        )
        c.execute(
            """INSERT INTO transactions(
                 telegram_id,kind,amount,balance_before,balance_after,reference,status,note
               ) VALUES(?,?,?,?,?,?,?,?)""",
            (
                row["telegram_id"],
                "REFUND",
                float(amount),
                float(before),
                float(after),
                ref,
                "COMPLETED",
                note,
            ),
        )
        c.execute(
            """UPDATE orders SET status='REFUNDED',delivery_error=?,updated_at=CURRENT_TIMESTAMP
               WHERE order_ref=?""",
            (note[:1000], order_ref),
        )
        c.commit()
        return "ok", after
    except sqlite3.IntegrityError:
        c.rollback()
        return "duplicate", None
    finally:
        c.close()


# -----------------------------------------------------------------------------
# Delivery state machine
# -----------------------------------------------------------------------------
def get_order(order_ref: str) -> Optional[sqlite3.Row]:
    c = db()
    r = c.execute("SELECT * FROM orders WHERE order_ref=?", (order_ref,)).fetchone()
    c.close()
    return r


def _claim_delivery(order_ref: str) -> Tuple[str, Optional[sqlite3.Row]]:
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT * FROM orders WHERE order_ref=?", (order_ref,)).fetchone()
        if not row:
            c.rollback()
            return "not-found", None
        if row["status"] == "COMPLETED":
            c.commit()
            return "completed", row
        if row["status"] == "DELIVERING":
            c.commit()
            return "busy", row
        if row["status"] != "PAID":
            c.commit()
            return "invalid-status", row
        c.execute(
            """UPDATE orders SET status='DELIVERING',delivery_attempts=COALESCE(delivery_attempts,0)+1,
               updated_at=CURRENT_TIMESTAMP WHERE order_ref=? AND status='PAID'""",
            (order_ref,),
        )
        c.commit()
        return "ok", get_order(order_ref)
    finally:
        c.close()


def _finish_delivery(order_ref: str, payload: list) -> None:
    c = db()
    c.execute(
        """UPDATE orders SET status='COMPLETED',delivery_payload=?,delivery_error=NULL,
           delivered_at=CURRENT_TIMESTAMP,updated_at=CURRENT_TIMESTAMP
           WHERE order_ref=?""",
        (json.dumps([str(x) for x in payload], ensure_ascii=False), order_ref),
    )
    c.commit()
    c.close()


def _mark_delivery_problem(order_ref: str, status: str, error: str) -> None:
    c = db()
    c.execute(
        """UPDATE orders SET status=?,delivery_error=?,updated_at=CURRENT_TIMESTAMP
           WHERE order_ref=?""",
        (status, error[:1000], order_ref),
    )
    c.commit()
    c.close()


def _delivery_lines(row: sqlite3.Row) -> list[str]:
    raw = row["delivery_payload"]
    if not raw:
        return []
    try:
        d = json.loads(raw)
        if isinstance(d, list):
            return [str(x) for x in d]
    except Exception:
        pass
    return [str(raw)]


def deliver_order(order_ref: str, notify: bool = True) -> str:
    claim, row = _claim_delivery(order_ref)
    if claim == "completed":
        if notify and row:
            deliver_order_message(row["telegram_id"], row)
        return "completed"
    if claim in {"busy", "invalid-status", "not-found"}:
        return claim
    if not row:
        return "not-found"

    cid = row["telegram_id"]
    supplier = (row["supplier"] or "AIVERSE").upper()

    try:
        if supplier == "OWN":
            products = finish_own_stock_delivery(order_ref, int(row["quantity"] or 1))
        else:
            # IMPORTANT: supplier ON/OFF is NOT checked here. An order that was already
            # paid/created stays locked to its original supplier and may finish safely.
            d = supplier_order(supplier, row["service_id"], int(row["quantity"] or 1))
            products = extract_delivery_payload(d, supplier)
            if not products:
                raise SupplierAmbiguous(f"{supplier} returned success but no product payload")
            _finish_delivery(order_ref, products)

        fresh = get_order(order_ref)
        if notify and fresh:
            deliver_order_message(cid, fresh)
        group_purchase_log(
            row["product_name"],
            row["quantity"],
            row["customer_price"],
        )
        return "completed"

    except SupplierRejected as e:
        msg = str(e)
        _mark_delivery_problem(order_ref, "DELIVERY_FAILED", msg)

        if supplier == "OWN":
            release_own_stock(order_ref)

        if row["payment_method"] == "BALANCE":
            _, bal = refund_balance_order_once(order_ref, f"Delivery rejected: {msg}")
            if notify:
                send(
                    cid,
                    f"⚠️ Automatic delivery failed.\n\nOrder: {order_ref}\n"
                    f"💵 ${fmoney(row['customer_price'])} USDT automatically refunded.\n"
                    f"Balance: ${fmoney(bal or get_balance(cid))}",
                )
            return "refunded"

        if notify:
            send(
                cid,
                f"✅ Payment is recorded.\n\n⚠️ Automatic delivery could not be completed for {order_ref}. "
                "Admin review is required; payment will not be charged twice.",
            )
        return "delivery-failed"

    except SupplierAmbiguous as e:
        msg = str(e)
        _mark_delivery_problem(order_ref, "DELIVERY_REVIEW", msg)
        if notify:
            send(
                cid,
                f"⚠️ Delivery status needs admin review.\n\nOrder: {order_ref}\n"
                "Your payment/order is recorded. The bot will not retry or refund automatically "
                "because the delivery result was uncertain, preventing duplicate delivery.",
            )
        return "review"

    except Exception as e:
        msg = f"Unexpected delivery error: {e}"
        _mark_delivery_problem(order_ref, "DELIVERY_REVIEW", msg)
        if notify:
            send(cid, f"⚠️ Order {order_ref} needs admin review. No automatic retry was made.")
        return "review"


def deliver_order_message(cid: Any, row: sqlite3.Row) -> None:
    codes = _delivery_lines(row)
    if not codes:
        send(cid, f"✅ Order {row['order_ref']} is completed, but delivery payload is unavailable.")
        return
    code_text = "\n".join("• " + x for x in codes)
    bal_text = ""
    if row["payment_method"] == "BALANCE":
        bal_text = f"\n\n💰 Balance: ${fmoney(get_balance(cid))} USDT"
    send(
        cid,
        f"🎉 Order Completed!\n\n🧾 {row['order_ref']}\n📦 {public_product_name(row['product_name'])}\n\n"
        f"🔑 Product / Activation:\n{code_text}{bal_text}\n\n"
        f"You can view this delivery again later with /order {row['order_ref']}.",
    )


# -----------------------------------------------------------------------------
# UI / customer flows
# -----------------------------------------------------------------------------
def main_menu(cid: Any) -> None:
    clear_state(cid)
    bal = get_balance(cid)
    kb = [
        [
            {"text": "🛍 Shop", "callback_data": "products"},
            {"text": "💎 Add Funds", "callback_data": "topup"},
        ],
        [
            {"text": "👛 Wallet", "callback_data": "wallet"},
            {"text": "🆘 Support", "callback_data": "support"},
        ],
        [{"text": "📦 My Orders", "callback_data": "orders"}],
    ]
    if is_admin(cid):
        kb.append([{"text": "🛠 Admin", "callback_data": "admin"}])
    send(
        cid,
        f"🏠 {SHOP_NAME}\n\n💰 Wallet Balance: ${fmoney(bal)} USDT\n\nChoose an option from the menu below.",
        kb,
    )


def wallet_menu(cid: Any) -> None:
    bal = get_balance(cid)
    kb = [
        [
            {"text": "💎 Add Funds", "callback_data": "topup"},
            {"text": "📜 Transactions", "callback_data": "transactions"},
        ],
        [
            {"text": "🛍 Shop", "callback_data": "products"},
            {"text": "🏠 Main Menu", "callback_data": "menu"},
        ],
    ]
    send(cid, f"👛 Wallet\n\n💰 Available Balance: ${fmoney(bal)} USDT", kb)


def support_ui(cid: Any) -> None:
    kb = []
    url = SUPPORT_URL
    if not url and SUPPORT_USERNAME:
        username = SUPPORT_USERNAME.lstrip("@")
        if username:
            url = f"https://t.me/{username}"
    if url:
        kb.append([{"text": "💬 Contact Support", "url": url}])
    kb.append([{"text": "🏠 Main Menu", "callback_data": "menu"}])
    send(cid, f"🆘 Support\n\n{SUPPORT_TEXT}", kb)



def _product_raw(x: dict) -> dict:
    raw = x.get("raw")
    return raw if isinstance(raw, dict) else {}


def _clean_public_text(value: Any, fallback: str = "") -> str:
    if value is None:
        return fallback
    if isinstance(value, (dict, list)):
        try:
            value = json.dumps(value, ensure_ascii=False)
        except Exception:
            value = str(value)
    s = str(value).strip()
    return s or fallback


def product_validity(x: dict) -> str:
    raw = _product_raw(x)
    for key in (
        "validity", "duration", "period", "validityText", "validity_text",
        "subscriptionPeriod", "subscription_period", "subscriptionDuration",
        "subscription_duration"
    ):
        if raw.get(key) not in (None, "", [], {}):
            return _clean_public_text(raw.get(key), "Not specified")

    name = public_product_name(x.get("name", ""))
    m = re.search(r"\b(\d+)\s*(?:m|mo|month|months)\b", name, re.I)
    if m:
        n = int(m.group(1))
        return f"{n} Month" if n == 1 else f"{n} Months"
    y = re.search(r"\b(\d+)\s*(?:y|yr|year|years)\b", name, re.I)
    if y:
        n = int(y.group(1))
        return f"{n} Year" if n == 1 else f"{n} Years"
    d = re.search(r"\b(\d+)\s*(?:d|day|days)\b", name, re.I)
    if d:
        n = int(d.group(1))
        return f"{n} Day" if n == 1 else f"{n} Days"
    return "Not specified"


def product_warranty(x: dict) -> str:
    raw = _product_raw(x)
    for key in (
        "warranty", "guarantee", "warrantyText", "warranty_text",
        "warrantyPeriod", "warranty_period"
    ):
        if raw.get(key) not in (None, "", [], {}):
            v = raw.get(key)
            if isinstance(v, bool):
                return "Warranty Included" if v else "No Warranty"
            return _clean_public_text(v, "No Warranty")
    return "No Warranty"


def product_note(x: dict) -> str:
    raw = _product_raw(x)
    for key in (
        "note", "notes", "description", "details", "instructions",
        "deliveryNote", "delivery_note"
    ):
        if raw.get(key) not in (None, "", [], {}):
            note = _clean_public_text(raw.get(key))
            # Avoid accidentally exposing backend/supplier identity in customer notes.
            note = re.sub(r"(?i)\b(aiverse|elite tools store|elite)\b", "Premium Hub", note)
            return note[:3500]
    return "No additional note is available for this product."


def product_stock_text(x: dict) -> str:
    stock = int(x.get("stock", 0) or 0)
    if stock <= 0:
        return "0"
    if stock >= 999999:
        return "Available"
    return str(stock)


def _qty_limit(x: dict) -> int:
    stock = int(x.get("stock", 0) or 0)
    if stock <= 0:
        return 1
    if stock >= 999999:
        return 100
    return max(1, min(stock, 100))


def _safe_qty(x: dict, quantity: Any) -> int:
    try:
        q = int(quantity)
    except Exception:
        q = 1
    return max(1, min(q, _qty_limit(x)))


_BOT_USERNAME_CACHE = ""


def _bot_username() -> str:
    global _BOT_USERNAME_CACHE
    if _BOT_USERNAME_CACHE:
        return _BOT_USERNAME_CACHE
    try:
        me = tg("getMe").get("result", {})
        _BOT_USERNAME_CACHE = str(me.get("username") or "")
    except Exception:
        _BOT_USERNAME_CACHE = ""
    return _BOT_USERNAME_CACHE


def product_share_link(token: str) -> str:
    username = _bot_username()
    if not username:
        return ""
    return f"https://t.me/{username}?start=product_{token}"


def products_ui(cid: Any, page: int = 0, force: bool = False) -> None:
    clear_state(cid)
    try:
        ss = customer_catalog(services(force=force))
        ss = sorted(ss, key=product_display_priority)

        total = len(ss)
        gemini_count = sum(1 for x in ss if is_featured_product(x))

        if total <= FIRST_PAGE_PRODUCTS:
            pages = 1
        else:
            remaining = total - FIRST_PAGE_PRODUCTS
            pages = 1 + ((remaining + PRODUCTS_PER_PAGE - 1) // PRODUCTS_PER_PAGE)

        page = max(0, min(int(page), pages - 1))

        if page == 0:
            start_i = 0
            end_i = FIRST_PAGE_PRODUCTS
        else:
            start_i = FIRST_PAGE_PRODUCTS + (page - 1) * PRODUCTS_PER_PAGE
            end_i = start_i + PRODUCTS_PER_PAGE

        shown = ss[start_i:end_i]
        kb = []

        main_offer = None
        if page == 0:
            # YOUR custom product always gets first priority when available.
            main_offer = next(
                (
                    x for x in ss
                    if str(x.get("supplier", "")).upper() == "OWN"
                    and int(x.get("stock", 0) or 0) > 0
                ),
                None,
            )
            if main_offer is None:
                main_offer = next(
                    (x for x in ss if is_main_product(x) and int(x.get("stock", 0) or 0) > 0),
                    None,
                )
            if main_offer is None:
                main_offer = next(
                    (x for x in ss if str(x.get("supplier", "")).upper() == "OWN"),
                    None,
                )
            if main_offer is None:
                main_offer = next((x for x in ss if is_main_product(x)), None)

            if main_offer is not None:
                key = str(
                    main_offer.get("product_key")
                    or _catalog_key(
                        main_offer.get("supplier", "AIVERSE"),
                        main_offer.get("product_id"),
                    )
                )
                name = public_product_name(main_offer.get("name", "Main Product"))
                cp = customer_price(main_offer)
                stock = int(main_offer.get("stock", 0) or 0)
                own_hero = str(main_offer.get("supplier", "")).upper() == "OWN"

                if own_hero and stock > 0:
                    hero_text = f"✨⭐ {name} — ${fmoney(cp)} ⭐✨"
                elif own_hero:
                    hero_text = f"🔴 {name} — ${fmoney(cp)}"
                elif stock > 0:
                    hero_text = f"⭐ {name} — ${fmoney(cp)}"
                else:
                    hero_text = f"🔴 {name} — ${fmoney(cp)}"

                kb.append([{"text": hero_text, "callback_data": f"product:{key}"}])

            if gemini_count:
                kb.append(
                    [{
                        "text": f"🔥 GEMINI OFFERS • {gemini_count} AVAILABLE/LISTED",
                        "callback_data": "noop",
                    }]
                )

        main_offer_key = None
        if page == 0 and main_offer is not None:
            main_offer_key = str(
                main_offer.get("product_key")
                or _catalog_key(
                    main_offer.get("supplier", "AIVERSE"),
                    main_offer.get("product_id"),
                )
            )

        for x in shown:
            key = str(
                x.get("product_key")
                or _catalog_key(x.get("supplier", "AIVERSE"), x.get("product_id"))
            )

            if page == 0 and main_offer_key and key == main_offer_key:
                continue

            name = public_product_name(x.get("name", "Unknown"))
            cp = customer_price(x)
            stock = int(x.get("stock", 0) or 0)
            own = str(x.get("supplier", "")).upper() == "OWN"

            if stock <= 0:
                icon = "🔴"
            elif own:
                icon = "✨⭐"
            elif is_featured_product(x):
                icon = "🔥"
            else:
                icon = "🛒"

            kb.append(
                [{
                    "text": f"{icon} {name} — ${fmoney(cp)}",
                    "callback_data": f"product:{key}",
                }]
            )

        nav = []
        if page > 0:
            nav.append({"text": "⬅️ Prev", "callback_data": f"products_page:{page-1}"})
        nav.append({"text": f"📄 {page+1}/{pages}", "callback_data": "noop"})
        if page + 1 < pages:
            nav.append({"text": "Next ➡️", "callback_data": f"products_page:{page+1}"})
        if nav:
            kb.append(nav)

        kb.append(
            [
                {"text": "🔄 Refresh", "callback_data": f"products_refresh:{page}"},
                {"text": "🏠 Menu", "callback_data": "menu"},
            ]
        )

        if page == 0:
            header = (
                "💎 <b>Premium Shop</b>\n"
                "━━━━━━━━━━━━━━━━━━\n"
                "🔥 Gemini offers follow next\n"
                "🟢 Available products are prioritized\n\n"
                f"📦 Total Products: {total}\n"
                f"📄 First Page: {min(FIRST_PAGE_PRODUCTS, total)} items"
            )
        else:
            header = (
                "🛍 <b>All Products</b>\n"
                "━━━━━━━━━━━━━━━━━━\n"
                f"📦 Total Products: {total}\n"
                f"📄 Page: {page+1}/{pages}"
            )

        send(cid, header, kb, parse_mode="HTML")

    except Exception as e:
        print("Product load error:", e)
        send(cid, "❌ Product load failed. Please try again.")


def _product_card(cid: Any, x: dict, key: str, qty: int) -> tuple[str, list]:
    qty = _safe_qty(x, qty)
    unit_price = customer_price(x)
    total = money(unit_price * qty)
    balance = get_balance(cid)
    stock = int(x.get("stock", 0) or 0)

    name = public_product_name(x.get("name", "Unknown"))
    validity = product_validity(x)
    warranty = product_warranty(x)
    stock_text = product_stock_text(x)

    if str(x.get("supplier", "")).upper() == "OWN":
        product_title = f"✨⭐ {name} ⭐✨"
    elif is_main_product(x):
        product_title = f"⭐ MAIN OFFER • {name}"
    elif is_featured_product(x):
        product_title = f"🔥 GEMINI OFFER • {name}"
    else:
        product_title = f"💎 {name}"

    stock_badge = "🟢 In Stock" if stock > 0 else "🔴 Out of Stock"

    body = (
        f"{product_title}\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        f"💵 Price: {fmoney(unit_price)} USDT\n"
        f"📅 Validity: {validity}\n"
        f"🛡 Warranty: {warranty}\n"
        f"📦 Available Stock: {stock_text}\n"
        f"📍 Status: {stock_badge}\n"
        f"🔢 Selected Qty: {qty}\n"
        f"🧾 Total: {fmoney(total)} USDT\n"
        f"👛 Wallet Balance: {fmoney(balance)} USDT\n\n"
        "✍️ Send a number to change quantity."
    )

    kb = []
    if stock > 0:
        kb = [[{"text": "🛒 Buy Now", "callback_data": f"buybal:{key}:{qty}"}]]

    return body, kb


def show_product(cid: Any, token: str, quantity: int = 1, force: bool = False) -> None:
    try:
        x = service(token, force=force)
        if not x:
            clear_state(cid)
            return send(cid, "❌ Product not found.")

        key = str(x.get("product_key") or token)
        qty = _safe_qty(x, quantity)
        body, kb = _product_card(cid, x, key, qty)

        result = send(cid, body, kb)
        mid = None
        try:
            mid = int(result.get("result", {}).get("message_id"))
        except Exception:
            mid = None

        set_state(
            cid,
            "PRODUCT_SELECTED",
            {
                "product_key": key,
                "quantity": qty,
                "message_id": mid,
            },
        )

    except Exception as e:
        print("Product details error:", e)
        send(cid, "❌ Product details failed.")

def topup_start(cid: Any) -> None:
    set_state(cid, "AWAIT_TOPUP_AMOUNT")
    kb = [
        [
            {"text": "💵 $0.01", "callback_data": "quicktopup:0.01"},
            {"text": "💵 $1", "callback_data": "quicktopup:1"},
            {"text": "💵 $5", "callback_data": "quicktopup:5"},
        ],
        [
            {"text": "💵 $10", "callback_data": "quicktopup:10"},
            {"text": "💵 $25", "callback_data": "quicktopup:25"},
            {"text": "💵 $50", "callback_data": "quicktopup:50"},
        ],
        [
            {"text": "👛 Wallet", "callback_data": "wallet"},
            {"text": "🏠 Main Menu", "callback_data": "menu"},
        ],
    ]
    send(
        cid,
        "💎 <b>Add Funds</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "💰 <b>Minimum Deposit:</b> $0.01 USDT\n"
        "⚡ <b>Payment:</b> Binance Pay\n"
        "🤖 <b>Verification:</b> Automatic\n\n"
        "✍️ <b>Enter the amount you want to add</b>\n"
        "Example: <code>0.01</code>, <code>5</code>, <code>10</code>, <code>25.5</code>\n\n"
        "Or choose a quick amount below.\n\n"
        "🏦 A Binance Pay UID will be generated automatically.\n"
        "🔐 Wallet credit is added only after successful verification.",
        kb,
        parse_mode="HTML",
    )

def create_topup(cid: Any, amount: Decimal) -> None:
    amount = money(amount)
    if amount < MIN_TOPUP:
        return send(cid, f"❌ Minimum top-up is ${fmoney(MIN_TOPUP)} USDT.")
    ref = new_ref("TOP")
    try:
        iid, uid = invoice(cid, amount)
        c = db()
        c.execute(
            """INSERT INTO topups(topup_ref,telegram_id,amount,invoice_id,payment_uid,status)
               VALUES(?,?,?,?,?,'PENDING')""",
            (ref, str(cid), float(amount), iid, uid),
        )
        c.commit()
        c.close()
        clear_state(cid)
        set_state(cid, "AWAIT_TOPUP_TX", {"ref": ref})
        send(
            cid,
            "🧾 <b>Payment Invoice</b>\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            f"🆔 <b>Invoice:</b> <code>{iid}</code>\n"
            f"💵 <b>Amount:</b> {fmoney(amount)} USDT\n"
            f"👤 <b>Binance UID:</b> <code>{uid}</code>\n\n"
            "1️⃣ Send the <b>exact amount</b> using Binance Pay.\n\n"
            "2️⃣ Paste your <b>TX / Order ID</b> here after payment.\n\n"
            "🤖 Verification and wallet credit are fully automatic.",
            [
                [{"text": "❌ Cancel Payment", "callback_data": "cancel_topup"}],
            ],
            parse_mode="HTML",
        )
        public_log("💳 New Top-up", f"Reference: {ref}\nAmount: ${fmoney(amount)} USDT\nStatus: PENDING")
    except Exception as e:
        print("Topup invoice error:", e)
        send(cid, "❌ Could not create the payment invoice. Please try again later.")


def verify_topup(cid: Any, ref: str, pid: str) -> None:
    c = db()
    row = c.execute(
        "SELECT * FROM topups WHERE topup_ref=? AND telegram_id=?",
        (ref, str(cid)),
    ).fetchone()
    c.close()

    if not row:
        clear_state(cid)
        return send(cid, "❌ Top-up not found.")

    if row["status"] == "PAID":
        clear_state(cid)
        return send(
            cid,
            f"ℹ️ This top-up has already been verified.\n"
            f"Balance: ${fmoney(get_balance(cid))}",
        )

    # Ensure the same invoice remains active while the customer retries a TX ID.
    set_state(cid, "AWAIT_TOPUP_TX", {"ref": ref})

    checking = send(cid, "🔍 Checking Payment...\n\n[1%] ▓░░░░░░░░░")
    mid = None
    try:
        mid = checking.get("result", {}).get("message_id")
    except Exception:
        mid = None

    try:
        for pct, bar in [
            ("10%", "▓▓░░░░░░░░"),
            ("25%", "▓▓▓░░░░░░░"),
            ("50%", "▓▓▓▓▓░░░░░"),
            ("75%", "▓▓▓▓▓▓▓░░"),
            ("100%", "▓▓▓▓▓▓▓▓▓▓"),
        ]:
            time.sleep(0.22)
            if mid:
                edit(cid, mid, f"🔍 Checking Payment...\n\n[{pct}] {bar}")
    except Exception:
        pass

    ok, data = verify_payhub(row["invoice_id"], pid)
    if not ok:
        if mid:
            try:
                edit(
                    cid,
                    mid,
                    "❌ Payment Declined\n\n"
                    "Invalid, unpaid, or unverified TX / Order ID.\n"
                    "You can paste the correct TX / Order ID again.",
                )
            except Exception:
                pass
        else:
            send(
                cid,
                "❌ Payment Declined\n\n"
                "Invalid, unpaid, or unverified TX / Order ID.\n"
                "You can paste the correct TX / Order ID again.",
            )
        return

    status, after = _topup_paid_once(ref, pid, data)

    if status in {"ok", "duplicate"}:
        clear_state(cid)
        if mid:
            try:
                edit(cid, mid, "✅ Payment Approved")
            except Exception:
                pass
        send(
            cid,
            f"✅ Balance Added\n\n"
            f"💰 Added: ${fmoney(row['amount'])} USDT\n"
            f"💳 New Balance: ${fmoney(after or get_balance(cid))} USDT",
        )
        if status == "ok":
            group_topup_log(row["amount"])
        return

    # Keep invoice state active for retryable verification errors.
    set_state(cid, "AWAIT_TOPUP_TX", {"ref": ref})

    messages = {
        "amount-mismatch": "❌ Payment amount mismatch. Balance was not added.",
        "currency-mismatch": "❌ Currency mismatch. Balance was not added.",
        "payment-already-used": "❌ This TX / Order ID has already been used for another payment.",
    }
    msg = messages.get(status, f"❌ Payment process failed: {status}")
    if mid:
        try:
            edit(cid, mid, msg + "\n\nYou can paste another TX / Order ID.")
            return
        except Exception:
            pass
    send(cid, msg + "\n\nYou can paste another TX / Order ID.")
def buy_balance(cid: Any, token: str, quantity: int = 1) -> None:
    try:
        x = service(token, force=True)
        if not x or int(x.get("stock", 0) or 0) <= 0:
            return send(cid, "❌ Product unavailable or out of stock.")

        try:
            quantity = _safe_qty(x, quantity)
            ref, cp, after = create_balance_order(cid, x, quantity)
        except ValueError as e:
            if str(e) == "INSUFFICIENT_BALANCE":
                return send(
                    cid,
                    f"❌ Insufficient balance.\n\n"
                    f"Total: ${fmoney(customer_price(x) * _safe_qty(x, quantity))}\n"
                    f"Balance: ${fmoney(get_balance(cid))}",
                    [[{"text": "💎 Add Funds", "callback_data": "topup"}]],
                )
            if str(e) == "OUT_OF_STOCK":
                return send(cid, "❌ Stock changed before checkout. Please reopen the product and try again.")
            raise

        send(
            cid,
            f"⏳ Order processing...\n\n"
            f"🧾 {ref}\n"
            f"📦 {public_product_name(x.get('name','Unknown'))}\n"
            f"🔢 Quantity: {quantity}\n"
            f"💰 ${fmoney(cp)} USDT",
        )
        deliver_order(ref)

    except Exception as e:
        print("Balance buy error:", e)
        send(cid, "❌ Order could not be created.")


def buy_direct(cid: Any, token: str, quantity: int = 1) -> None:
    ref = ""
    supplier = ""
    try:
        x = service(token, force=True)
        if not x or int(x.get("stock", 0) or 0) <= 0:
            return send(cid, "❌ Product unavailable or out of stock.")

        sid = str(x.get("product_id") or x.get("service_id"))
        supplier = str(x.get("supplier", "AIVERSE")).upper()
        product_key = str(x.get("product_key") or (_catalog_key(supplier, sid) if supplier != "OWN" else sid))
        name = str(x.get("name", "Unknown"))
        quantity = _safe_qty(x, quantity)

        cp_unit = customer_price(x)
        cp = money(cp_unit * quantity)
        sp_unit = Decimal("0.00") if supplier == "OWN" else money(x.get("price", 0))
        sp = money(sp_unit * quantity)
        ref = new_ref("ORD")

        c = db()
        try:
            c.execute("BEGIN IMMEDIATE")
            if supplier == "OWN":
                _reserve_own_stock_tx(c, product_key, quantity, ref)
            c.execute(
                """INSERT INTO orders(
                     order_ref,telegram_id,service_id,product_name,quantity,supplier_price,
                     customer_price,status,payment_method,supplier,product_key
                   ) VALUES(?,?,?,?,?,?,?,?,?,?,?)""",
                (
                    ref, str(cid), sid, name, quantity, float(sp), float(cp),
                    "CREATING_INVOICE", "DIRECT", supplier, product_key
                ),
            )
            c.commit()
        except Exception:
            c.rollback()
            raise
        finally:
            c.close()

        try:
            iid, uid = invoice(cid, cp)
        except Exception as e:
            if supplier == "OWN":
                release_own_stock(ref)
            c = db()
            c.execute(
                """UPDATE orders SET status='INVOICE_FAILED',delivery_error=?,
                   updated_at=CURRENT_TIMESTAMP WHERE order_ref=?""",
                (str(e)[:1000], ref),
            )
            c.commit()
            c.close()
            raise

        c = db()
        c.execute(
            """UPDATE orders SET invoice_id=?,payment_uid=?,status='PENDING_PAYMENT',
               updated_at=CURRENT_TIMESTAMP WHERE order_ref=?""",
            (iid, uid, ref),
        )
        c.commit()
        c.close()

        send(
            cid,
            f"🧾 Direct Payment Invoice\n\n"
            f"📦 {public_product_name(name)}\n"
            f"🔢 Quantity: {quantity}\n"
            f"💵 Amount: ${fmoney(cp)} USDT\n"
            f"🆔 Invoice: {iid}\n"
            f"👤 Binance UID: {uid or '-'}\n\n"
            "Pay the exact amount. After automatic verification, delivery starts automatically.",
        )
    except ValueError as e:
        if str(e) == "OUT_OF_STOCK":
            send(cid, "❌ Stock changed before invoice creation. Please try again.")
        else:
            send(cid, "❌ Could not create the direct payment invoice.")
    except Exception as e:
        print("Direct buy error:", e)
        send(cid, "❌ Could not create the direct payment invoice.")


def verify_direct(cid: Any, order_ref: str, pid: str) -> None:
    c = db()
    row = c.execute(
        "SELECT * FROM orders WHERE order_ref=? AND telegram_id=?", (order_ref, str(cid))
    ).fetchone()
    c.close()
    if not row:
        return send(cid, "❌ Order not found.")
    if row["payment_method"] != "DIRECT":
        return send(cid, "❌ This is not a direct-payment order.")
    if row["status"] == "COMPLETED":
        return deliver_order_message(cid, row)
    if row["status"] not in {"PENDING_PAYMENT", "PAID", "DELIVERING", "DELIVERY_REVIEW", "DELIVERY_FAILED"}:
        return send(cid, f"ℹ️ Order status: {row['status']}")
    if row["status"] != "PENDING_PAYMENT":
        return send(cid, f"ℹ️ Payment already recorded. Order status: {row['status']}")

    ok, data = verify_payhub(row["invoice_id"], pid)
    if not ok:
        return send(cid, "⏳ Payment not verified yet. Check the Transaction / Order ID and try again.")
    status = _mark_direct_paid_once(order_ref, pid, data)
    if status in {"ok", "duplicate"}:
        send(cid, "✅ Payment verified!\n\n📦 Delivery process started...")
        deliver_order(order_ref)
    elif status == "amount-mismatch":
        send(cid, "❌ Payment amount mismatch. Delivery was not started.")
    elif status == "currency-mismatch":
        send(cid, "❌ Currency mismatch. Delivery was not started.")
    elif status == "payment-already-used":
        send(cid, "❌ This transaction/order ID has already been used for another payment.")
    else:
        send(cid, f"❌ Payment verification failed: {status}")


def verify_direct_legacy(cid: Any, pid: str) -> None:
    c = db()
    row = c.execute(
        """SELECT order_ref FROM orders WHERE telegram_id=? AND payment_method='DIRECT'
           AND status='PENDING_PAYMENT' ORDER BY id DESC LIMIT 1""",
        (str(cid),),
    ).fetchone()
    c.close()
    if not row:
        return send(cid, "❌ No pending direct payment found.")
    verify_direct(cid, row["order_ref"], pid)


def show_orders(cid: Any) -> None:
    c = db()
    rows = c.execute(
        "SELECT * FROM orders WHERE telegram_id=? ORDER BY id DESC LIMIT 10", (str(cid),)
    ).fetchall()
    c.close()
    if not rows:
        return send(cid, "📦 No orders yet.")
    lines = ["📦 My Orders", ""]
    for r in rows:
        lines.append(
            f"• {r['order_ref']} | {public_product_name(r['product_name'])} | ${fmoney(r['customer_price'])} | {r['status']}"
        )
    lines.extend(["", "View a completed delivery with: /order ORDER_REF"])
    send(cid, "\n".join(lines))


def show_order(cid: Any, ref: str) -> None:
    c = db()
    row = c.execute(
        "SELECT * FROM orders WHERE order_ref=? AND telegram_id=?", (ref, str(cid))
    ).fetchone()
    c.close()
    if not row:
        return send(cid, "❌ Order not found.")
    if row["status"] == "COMPLETED":
        return deliver_order_message(cid, row)
    send(
        cid,
        f"🧾 Order: {row['order_ref']}\n📦 {public_product_name(row['product_name'])}\n"
        f"💰 ${fmoney(row['customer_price'])} USDT\n📌 Status: {row['status']}",
    )


def show_transactions(cid: Any) -> None:
    c = db()
    rows = c.execute(
        "SELECT * FROM transactions WHERE telegram_id=? ORDER BY id DESC LIMIT 15", (str(cid),)
    ).fetchall()
    c.close()
    if not rows:
        return send(cid, "📜 No transactions yet.")
    text = "📜 Transactions\n\n" + "\n".join(
        f"• {r['kind']} | {'+' if r['amount'] > 0 else ''}{float(r['amount']):.2f} | {r['created_at']}"
        for r in rows
    )
    send(cid, text)


# -----------------------------------------------------------------------------
# Admin
# -----------------------------------------------------------------------------
def is_admin(cid: Any) -> bool:
    return str(cid) in ADMIN_IDS


def admin_panel(cid: Any) -> None:
    if not is_admin(cid):
        return send(cid, "⛔ Admin only.")

    aiv = "🟢 ON" if supplier_enabled("AIVERSE") else "🔴 OFF"
    ets = "🟢 ON" if supplier_enabled("ELITE") else "🔴 OFF"

    kb = [
        [
            {"text": "📊 Overview", "callback_data": "adm:stats"},
            {"text": "👥 Users", "callback_data": "adm:users"},
        ],
        [
            {"text": "📦 Orders", "callback_data": "adm:orders"},
            {"text": "💳 Payments", "callback_data": "adm:pending"},
        ],
        [
            {"text": "🔌 Supplier Control", "callback_data": "adm:suppliers"},
            {"text": "⭐ Custom Products", "callback_data": "adm:custom"},
        ],
        [
            {"text": "📜 Transactions", "callback_data": "adm:transactions"},
            {"text": "🛡 Delivery Review", "callback_data": "adm:review"},
        ],
        [{"text": "📣 Notify All Users", "callback_data": "adm:broadcast"}],
        [{"text": "🏠 Main Menu", "callback_data": "menu"}],
    ]

    send(
        cid,
        "🛠 <b>Admin Control Center</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        f"🔹 AIVerse: <b>{aiv}</b>\n"
        f"🔹 Elite: <b>{ets}</b>\n"
        "⭐ Own Stock: <b>Enabled</b>\n\n"
        "Supplier switches affect <b>new</b> orders only.\n"
        "Already-paid orders stay locked to their original delivery source.",
        kb,
        parse_mode="HTML",
    )


def admin_stats(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    users = c.execute("SELECT COUNT(*) n FROM users").fetchone()["n"]
    bal = c.execute("SELECT COALESCE(SUM(balance),0) s FROM users").fetchone()["s"]
    orders = c.execute("SELECT COUNT(*) n FROM orders").fetchone()["n"]
    completed = c.execute("SELECT COUNT(*) n FROM orders WHERE status='COMPLETED'").fetchone()["n"]
    pending = c.execute("SELECT COUNT(*) n FROM topups WHERE status='PENDING'").fetchone()["n"]
    direct_pending = c.execute(
        "SELECT COUNT(*) n FROM orders WHERE status='PENDING_PAYMENT'"
    ).fetchone()["n"]
    review = c.execute(
        "SELECT COUNT(*) n FROM orders WHERE status IN ('DELIVERY_REVIEW','DELIVERY_FAILED')"
    ).fetchone()["n"]
    custom_products_n = c.execute("SELECT COUNT(*) n FROM custom_products").fetchone()["n"]
    own_available = c.execute(
        "SELECT COUNT(*) n FROM custom_stock WHERE status='AVAILABLE'"
    ).fetchone()["n"]
    own_delivered = c.execute(
        "SELECT COUNT(*) n FROM custom_stock WHERE status='DELIVERED'"
    ).fetchone()["n"]
    c.close()
    send(
        cid,
        f"📊 Statistics\n\n👥 Users: {users}\n💰 Total User Balance: ${float(bal):.2f}\n"
        f"📦 Orders: {orders}\n✅ Completed: {completed}\n"
        f"⏳ Pending Top-ups: {pending}\n💳 Pending Direct Payments: {direct_pending}\n"
        f"🛡 Delivery Review: {review}\n"
        f"⭐ Custom Products: {custom_products_n}\n"
        f"📦 Own Stock Available: {own_available}\n"
        f"📤 Own Stock Delivered: {own_delivered}",
    )


def _send_lines(cid: Any, title: str, lines: list[str], empty: str) -> None:
    if not lines:
        return send(cid, empty)
    # Telegram message hard limit is 4096; keep each page comfortably below it.
    page = title + "\n\n"
    for line in lines:
        if len(page) + len(line) + 1 > 3600:
            send(cid, page.rstrip())
            page = title + " (cont.)\n\n"
        page += line + "\n"
    if page.strip():
        send(cid, page.rstrip())


def admin_users(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    rows = c.execute(
        "SELECT telegram_id,username,first_name,balance,last_seen FROM users ORDER BY last_seen DESC LIMIT 30"
    ).fetchall()
    c.close()
    lines = [
        f"• ID: {r['telegram_id']} | @{r['username'] or '-'} | {r['first_name']} | ${float(r['balance']):.2f}"
        for r in rows
    ]
    _send_lines(cid, "👥 Users (latest 30)", lines, "No users.")


def admin_orders(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    rows = c.execute("SELECT * FROM orders ORDER BY id DESC LIMIT 30").fetchall()
    c.close()
    lines = [
        f"• {r['order_ref']} | [{r['supplier'] or 'AIVERSE'}] {r['product_name']} | ${fmoney(r['customer_price'])} | "
        f"{r['status']} | {r['payment_method']} | UID {r['telegram_id']}"
        for r in rows
    ]
    _send_lines(cid, "📦 Latest Orders", lines, "No orders.")


def admin_pending(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    tops = c.execute(
        "SELECT * FROM topups WHERE status='PENDING' ORDER BY id DESC LIMIT 20"
    ).fetchall()
    orders = c.execute(
        """SELECT * FROM orders WHERE payment_method='DIRECT' AND status='PENDING_PAYMENT'
           ORDER BY id DESC LIMIT 20"""
    ).fetchall()
    c.close()
    lines = []
    lines.extend(
        f"• TOPUP {r['topup_ref']} | User {r['telegram_id']} | ${fmoney(r['amount'])} | {r['invoice_id']}"
        for r in tops
    )
    lines.extend(
        f"• ORDER {r['order_ref']} | User {r['telegram_id']} | ${fmoney(r['customer_price'])} | {r['invoice_id']}"
        for r in orders
    )
    _send_lines(cid, "💳 Pending Payments", lines, "✅ No pending payments.")


def admin_transactions(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    rows = c.execute(
        """SELECT telegram_id,kind,amount,balance_before,balance_after,reference,status,created_at
           FROM transactions ORDER BY id DESC LIMIT 40"""
    ).fetchall()
    c.close()
    lines = [
        f"• {r['created_at']} | User {r['telegram_id']} | {r['kind']} | "
        f"{float(r['amount']):+.2f} | Bal ${float(r['balance_after']):.2f} | "
        f"{r['reference']} | {r['status']}"
        for r in rows
    ]
    _send_lines(cid, "📜 Latest Transactions", lines, "No transactions.")


def admin_review(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    rows = c.execute(
        """SELECT * FROM orders WHERE status IN ('DELIVERY_REVIEW','DELIVERY_FAILED')
           ORDER BY id DESC LIMIT 30"""
    ).fetchall()
    c.close()
    lines = [
        f"• {r['order_ref']} | {r['product_name']} | {r['status']} | "
        f"{(r['delivery_error'] or '-')[:100]}"
        for r in rows
    ]
    _send_lines(cid, "🛡 Delivery Review Queue", lines, "✅ No delivery-review orders.")


def admin_suppliers(cid: Any) -> None:
    if not is_admin(cid):
        return

    aiv_on = supplier_enabled("AIVERSE")
    ets_on = supplier_enabled("ELITE")

    lines = [
        "🔌 <b>Supplier Control</b>",
        "━━━━━━━━━━━━━━━━━━",
        "",
        f"🔹 AIVerse: <b>{'🟢 ON' if aiv_on else '🔴 OFF'}</b>",
        f"🔹 Elite Tools: <b>{'🟢 ON' if ets_on else '🔴 OFF'}</b>",
        "",
        "Turning a supplier OFF:",
        "• hides its products from new customers",
        "• blocks checkout from old product buttons",
        "• does NOT affect Wallet/Top-up/PayHub",
        "• does NOT interrupt an order that was already paid/created",
    ]

    kb = [
        [
            {
                "text": "🔴 Turn OFF AIVerse" if aiv_on else "🟢 Turn ON AIVerse",
                "callback_data": "adm:supplier_toggle:AIVERSE",
            }
        ],
        [
            {
                "text": "🔴 Turn OFF Elite" if ets_on else "🟢 Turn ON Elite",
                "callback_data": "adm:supplier_toggle:ELITE",
            }
        ],
        [{"text": "🧪 Test Enabled Suppliers", "callback_data": "adm:supplier_test"}],
        [{"text": "◀️ Admin Panel", "callback_data": "admin"}],
    ]
    send(cid, "\n".join(lines), kb, parse_mode="HTML")



def admin_custom_products(cid: Any) -> None:
    if not is_admin(cid):
        return

    c = db()
    rows = c.execute(
        """SELECT p.*,
          COALESCE(SUM(CASE WHEN s.status='AVAILABLE' THEN 1 ELSE 0 END),0) available,
          COALESCE(SUM(CASE WHEN s.status='RESERVED' THEN 1 ELSE 0 END),0) reserved,
          COALESCE(SUM(CASE WHEN s.status='DELIVERED' THEN 1 ELSE 0 END),0) delivered
        FROM custom_products p
        LEFT JOIN custom_stock s ON s.product_key=p.product_key
        GROUP BY p.product_key
        ORDER BY p.created_at DESC"""
    ).fetchall()
    c.close()

    kb = []
    for r in rows[:25]:
        status = "🟢" if int(r["enabled"] or 0) else "🔴"
        kb.append(
            [{
                "text": f"{status} ⭐ {public_product_name(r['name'])} • Stock {int(r['available'])}",
                "callback_data": f"adm:custom_view:{r['product_key']}",
            }]
        )

    kb.append([{"text": "➕ Add Custom Product", "callback_data": "adm:custom_add"}])
    kb.append([{"text": "◀️ Admin Panel", "callback_data": "admin"}])

    send(
        cid,
        "⭐ Custom / Own-Stock Products\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "Your enabled own-stock products are pinned before supplier products.\n"
        "Each stock item is delivered only once.",
        kb,
    )


def admin_custom_view(cid: Any, product_key: str) -> None:
    if not is_admin(cid):
        return
    row = _custom_product_row(product_key)
    if not row:
        return send(cid, "❌ Custom product not found.")

    counts = _custom_stock_counts(product_key)
    enabled = bool(int(row["enabled"] or 0))

    kb = [
        [
            {"text": "➕ Add Stock", "callback_data": f"adm:custom_stock:{product_key}"},
            {"text": "💵 Edit Price", "callback_data": f"adm:custom_price:{product_key}"},
        ],
        [
            {"text": "✏️ Edit Name", "callback_data": f"adm:custom_name:{product_key}"},
            {"text": "📅 Edit Validity", "callback_data": f"adm:custom_validity:{product_key}"},
        ],
        [
            {"text": "🛡 Edit Warranty", "callback_data": f"adm:custom_warranty:{product_key}"},
        ],
        [
            {
                "text": "🔴 Disable Product" if enabled else "🟢 Enable Product",
                "callback_data": f"adm:custom_toggle:{product_key}",
            }
        ],
        [{"text": "◀️ Custom Products", "callback_data": "adm:custom"}],
    ]

    send(
        cid,
        "⭐ OWN-STOCK PRODUCT\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        f"📦 {public_product_name(row['name'])}\n"
        f"💵 Price: ${fmoney(row['price'])}\n"
        f"📅 Validity: {row['validity'] or '-'}\n"
        f"🛡 Warranty: {row['warranty'] or 'No Warranty'}\n"
        f"🔌 Status: {'🟢 Enabled' if enabled else '🔴 Disabled'}\n\n"
        f"✅ Available: {counts.get('AVAILABLE',0)}\n"
        f"🟡 Reserved: {counts.get('RESERVED',0)}\n"
        f"📤 Delivered: {counts.get('DELIVERED',0)}\n\n"
        "🔐 Stock lifecycle: AVAILABLE → RESERVED → DELIVERED",
        kb,
    )


def admin_custom_add_start(cid: Any) -> None:
    clear_state(cid)
    set_state(cid, "ADMIN_CUSTOM_NAME", {})
    send(
        cid,
        "➕ Add Custom Product\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "Step 1/4 — Send the product name.\n\n"
        "Example: Gemini Jio 18 Months",
    )


def admin_custom_stock_start(cid: Any, product_key: str) -> None:
    row = _custom_product_row(product_key)
    if not row:
        return send(cid, "❌ Custom product not found.")
    clear_state(cid)
    set_state(cid, "ADMIN_CUSTOM_STOCK", {"product_key": product_key})
    send(
        cid,
        "📦 Add Own Stock\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        f"Product: {public_product_name(row['name'])}\n\n"
        "Paste stock now — one delivery item per line.\n"
        "You can use a link, code, or email | password.\n\n"
        "Example:\n"
        "https://activation-link-1\n"
        "CODE-ABC-123\n"
        "mail@example.com | password123",
    )


def admin_custom_price_start(cid: Any, product_key: str) -> None:
    row = _custom_product_row(product_key)
    if not row:
        return send(cid, "❌ Custom product not found.")
    clear_state(cid)
    set_state(cid, "ADMIN_CUSTOM_PRICE_EDIT", {"product_key": product_key})
    send(
        cid,
        f"💵 Edit Price\n\nCurrent: ${fmoney(row['price'])} USDT\n\n"
        "Send the new USDT price.",
    )


def admin_custom_name_start(cid: Any, product_key: str) -> None:
    row = _custom_product_row(product_key)
    if not row:
        return send(cid, "❌ Custom product not found.")
    clear_state(cid)
    set_state(cid, "ADMIN_CUSTOM_NAME_EDIT", {"product_key": product_key})
    send(
        cid,
        f"✏️ Edit Product Name\n\nCurrent: {public_product_name(row['name'])}\n\n"
        "Send the new product name.",
    )


def admin_custom_validity_start(cid: Any, product_key: str) -> None:
    row = _custom_product_row(product_key)
    if not row:
        return send(cid, "❌ Custom product not found.")
    clear_state(cid)
    set_state(cid, "ADMIN_CUSTOM_VALIDITY_EDIT", {"product_key": product_key})
    send(
        cid,
        "📅 Edit Validity\n\n"
        f"Current: {row['validity'] or '-'}\n\n"
        "Send the correct validity, for example: 18 Months\n"
        "Send - if you want to clear the validity field.",
    )


def admin_custom_warranty_start(cid: Any, product_key: str) -> None:
    row = _custom_product_row(product_key)
    if not row:
        return send(cid, "❌ Custom product not found.")
    clear_state(cid)
    set_state(cid, "ADMIN_CUSTOM_WARRANTY_EDIT", {"product_key": product_key})
    send(
        cid,
        "🛡 Edit Warranty\n\n"
        f"Current: {row['warranty'] or 'No Warranty'}\n\n"
        "Send the new warranty, for example: No Warranty\n"
        "Send - if you want to clear it.",
    )


def handle_admin_state(cid: Any, state: str, data: dict, text_value: str) -> bool:
    if not is_admin(cid) or not state.startswith("ADMIN_"):
        return False

    value = str(text_value or "").strip()

    if state == "ADMIN_CUSTOM_NAME":
        if not value:
            send(cid, "❌ Product name cannot be empty.")
            return True
        set_state(cid, "ADMIN_CUSTOM_PRICE", {"name": value})
        send(cid, "Step 2/4 — Send the customer price in USDT.\nExample: 0.32")
        return True

    if state == "ADMIN_CUSTOM_PRICE":
        try:
            price = money(value)
            if price <= 0:
                raise ValueError
        except Exception:
            send(cid, "❌ Send a valid positive price, for example: 0.32")
            return True
        payload = dict(data)
        payload["price"] = str(price)
        set_state(cid, "ADMIN_CUSTOM_VALIDITY", payload)
        send(cid, "Step 3/4 — Send validity.\nExample: 18 Months")
        return True

    if state == "ADMIN_CUSTOM_VALIDITY":
        payload = dict(data)
        payload["validity"] = "" if value == "-" else (value or "Not specified")
        set_state(cid, "ADMIN_CUSTOM_WARRANTY", payload)
        send(cid, "Step 4/4 — Send warranty.\nExample: No Warranty")
        return True

    if state == "ADMIN_CUSTOM_WARRANTY":
        try:
            key = create_custom_product(
                data.get("name", "Custom Product"),
                data.get("price", "0"),
                data.get("validity", ""),
                "" if value == "-" else (value or "No Warranty"),
            )
            clear_state(cid)
            send(cid, "✅ Custom product created.\n\nNow add stock before customers can buy it.")
            admin_custom_view(cid, key)
        except Exception as e:
            print("Custom product create error:", e)
            clear_state(cid)
            send(cid, "❌ Could not create custom product.")
        return True

    if state == "ADMIN_CUSTOM_STOCK":
        key = str(data.get("product_key") or "")
        row = _custom_product_row(key)
        if not row:
            clear_state(cid)
            send(cid, "❌ Custom product not found.")
            return True

        payloads = [line.strip() for line in value.splitlines() if line.strip()]
        if not payloads:
            send(cid, "❌ Send at least one stock item.")
            return True

        added, skipped = add_custom_stock(key, payloads)
        clear_state(cid)
        send(
            cid,
            f"✅ Stock updated.\n\n"
            f"➕ Added: {added}\n"
            f"⏭ Duplicates skipped: {skipped}",
        )
        admin_custom_view(cid, key)
        return True

    if state == "ADMIN_CUSTOM_PRICE_EDIT":
        key = str(data.get("product_key") or "")
        try:
            price = money(value)
            if price <= 0:
                raise ValueError
            c = db()
            c.execute(
                """UPDATE custom_products
                   SET price=?,updated_at=CURRENT_TIMESTAMP
                   WHERE product_key=?""",
                (float(price), key),
            )
            c.commit()
            c.close()
            clear_state(cid)
            send(cid, f"✅ Price updated to ${fmoney(price)} USDT.")
            admin_custom_view(cid, key)
        except Exception:
            send(cid, "❌ Send a valid positive USDT price.")
        return True

    if state == "ADMIN_CUSTOM_NAME_EDIT":
        key = str(data.get("product_key") or "")
        if not value:
            send(cid, "❌ Product name cannot be empty.")
            return True
        c = db()
        c.execute(
            """UPDATE custom_products
               SET name=?,updated_at=CURRENT_TIMESTAMP
               WHERE product_key=?""",
            (value, key),
        )
        c.commit()
        c.close()
        clear_state(cid)
        send(cid, "✅ Product name updated.")
        admin_custom_view(cid, key)
        return True

    if state == "ADMIN_CUSTOM_VALIDITY_EDIT":
        key = str(data.get("product_key") or "")
        new_value = "" if value == "-" else value
        c = db()
        c.execute(
            """UPDATE custom_products
               SET validity=?,updated_at=CURRENT_TIMESTAMP
               WHERE product_key=?""",
            (new_value, key),
        )
        c.commit()
        c.close()
        clear_state(cid)
        send(cid, "✅ Validity updated.")
        admin_custom_view(cid, key)
        return True

    if state == "ADMIN_CUSTOM_WARRANTY_EDIT":
        key = str(data.get("product_key") or "")
        new_value = "" if value == "-" else (value or "No Warranty")
        c = db()
        c.execute(
            """UPDATE custom_products
               SET warranty=?,updated_at=CURRENT_TIMESTAMP
               WHERE product_key=?""",
            (new_value, key),
        )
        c.commit()
        c.close()
        clear_state(cid)
        send(cid, "✅ Warranty updated.")
        admin_custom_view(cid, key)
        return True

    return False


def broadcast_prompt(cid: Any) -> None:
    if not is_admin(cid):
        return
    c = db()
    total_users = c.execute("SELECT COUNT(*) AS n FROM users").fetchone()["n"]
    c.execute(
        "INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",
        (f"broadcast:{cid}", "1"),
    )
    c.commit()
    c.close()
    send(
        cid,
        f"📣 Send Notification to All Users\n\n"
        f"Registered users: {total_users}\n\n"
        "Now send the text, photo, video, document, or other Telegram message you want to send. "
        "The next message will be copied to every registered user.\n\n"
        "Cancel with /cancelbroadcast.",
    )

def do_broadcast(m: dict) -> bool:
    cid = str(m.get("chat", {}).get("id"))
    if not is_admin(cid):
        return False
    key = f"broadcast:{cid}"
    c = db()
    mode = c.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    c.close()
    if not mode:
        return False

    text = (m.get("text") or "").strip()
    if text == "/cancelbroadcast":
        c = db()
        c.execute("DELETE FROM settings WHERE key=?", (key,))
        c.commit()
        c.close()
        send(cid, "✅ Notification cancelled.")
        return True

    c = db()
    users = [r["telegram_id"] for r in c.execute("SELECT telegram_id FROM users").fetchall()]
    c.close()
    ok = fail = 0
    for uid in users:
        try:
            tg(
                "copyMessage",
                {"chat_id": uid, "from_chat_id": cid, "message_id": m["message_id"]},
            )
            ok += 1
        except Exception as e:
            fail += 1
            print("Broadcast fail", uid, e)
        time.sleep(0.04)

    c = db()
    c.execute("DELETE FROM settings WHERE key=?", (key,))
    c.commit()
    c.close()
    send(cid, f"📣 Notification complete\n\n✅ Sent: {ok}\n❌ Failed: {fail}")
    public_log("📣 Admin Notification", f"Sent: {ok}\nFailed: {fail}")
    return True


# -----------------------------------------------------------------------------
# PayHub webhook
# -----------------------------------------------------------------------------
def webhook_process(p: dict) -> str:
    event = str(p.get("event", "")).upper()
    status = str(p.get("status", "")).upper()
    if event and event not in {"PAYMENT_PAID", "PAYMENT_SUCCESS", "PAYMENT_COMPLETED"}:
        return "ignored"
    if status and status not in _PAYMENT_OK:
        return "not-paid"

    iid = p.get("invoice_id") or p.get("invoiceId") or p.get("invoice_no")
    if not iid:
        return "unknown-invoice"
    iid = str(iid)
    payment_id = str(p.get("txid") or p.get("order_id") or p.get("tx_id") or f"WEBHOOK:{iid}")

    c = db()
    top = c.execute("SELECT * FROM topups WHERE invoice_id=?", (iid,)).fetchone()
    order_row = c.execute("SELECT * FROM orders WHERE invoice_id=?", (iid,)).fetchone()
    c.close()

    if top:
        result, after = _topup_paid_once(top["topup_ref"], payment_id, p)
        if result == "ok":
            try:
                clear_state(top["telegram_id"])
            except Exception:
                pass
            try:
                send(
                    top["telegram_id"],
                    f"✅ Payment Received\n\n💰 Added: ${fmoney(top['amount'])} USDT\n"
                    f"💳 Balance: ${fmoney(after or get_balance(top['telegram_id']))} USDT",
                )
            except Exception as e:
                print("Topup notification error:", e)
            group_topup_log(top["amount"])
        return result

    if order_row:
        if order_row["payment_method"] != "DIRECT":
            return "order-invoice-invalid-method"
        result = _mark_direct_paid_once(order_row["order_ref"], payment_id, p)
        if result in {"ok", "duplicate"}:
            fresh = get_order(order_row["order_ref"])
            if fresh and fresh["status"] == "PAID":
                try:
                    send(fresh["telegram_id"], "✅ Payment Received\n\n📦 Delivery process started...")
                except Exception as e:
                    print("Direct payment notification error:", e)
                deliver_order(fresh["order_ref"])
            return "ok" if result == "ok" else "duplicate"
        return result

    return "unknown-invoice"


def start_webhook() -> None:
    try:
        from flask import Flask, jsonify, request
    except ImportError:
        print("Flask not installed; webhook disabled.")
        return

    app = Flask(__name__)

    @app.get("/")
    @app.get("/health")
    def health():
        return jsonify({"ok": True, "service": "digital-shop-bot"}), 200

    @app.post("/api/v1/payments/webhook")
    @app.post("/webhook")
    @app.post("/ipn")
    def wh():
        provided = request.headers.get("X-Webhook-Secret", "")
        if not hmac.compare_digest(provided, PAYMENT_WEBHOOK_SECRET):
            return jsonify({"error": "invalid-secret"}), 401
        try:
            result = webhook_process(request.get_json(silent=True) or {})
            return jsonify({"result": result}), 200
        except Exception as e:
            print("Webhook error:", e)
            return jsonify({"error": "internal-error"}), 500

    try:
        from waitress import serve
        print(f"🌐 Webhook server: Waitress on {WEBHOOK_HOST}:{WEBHOOK_PORT}")
        serve(app, host=WEBHOOK_HOST, port=WEBHOOK_PORT, threads=4)
    except ImportError:
        print("⚠️ Waitress not installed; falling back to Flask development server.")
        app.run(host=WEBHOOK_HOST, port=WEBHOOK_PORT, debug=False, use_reloader=False)


# -----------------------------------------------------------------------------
# Telegram update handlers
# -----------------------------------------------------------------------------
def callback(q: dict) -> None:
    msg = q.get("message", {}) or {}
    chat = msg.get("chat", {}) or {}

    # Never open shop/join/admin UI from group or supergroup messages.
    if chat.get("type") != "private":
        answer(q.get("id", ""))
        return

    user = q.get("from", {})
    upsert_user_from_user(user)
    cid = str(chat.get("id"))
    data = q.get("data", "")
    answer(q.get("id", ""))

    # Security gate: all admin callback actions are restricted at the dispatcher,
    # not only inside individual helper functions.
    if (data == "admin" or data.startswith("adm:")) and not is_admin(cid):
        return send(cid, "⛔ Admin only.")

    # Admin control callbacks do not depend on the customer force-join gate.
    if not is_admin(cid) and not joined(cid) and data != "verify_join":
        return join_gate(cid)

    if data == "verify_join":
        if joined(cid):
            answer(q.get("id", ""), "Verified!")
            main_menu(cid)
        else:
            answer(q.get("id", ""), "Join both first.")
            join_gate(cid)
    elif data == "menu":
        clear_state(cid)
        main_menu(cid)
    elif data == "products":
        products_ui(cid, 0)
    elif data.startswith("products_page:"):
        try:
            products_ui(cid, int(data.split(":", 1)[1]))
        except Exception:
            products_ui(cid, 0)
    elif data == "products_refresh":
        products_ui(cid, 0, force=True)
    elif data.startswith("products_refresh:"):
        try:
            products_ui(cid, int(data.split(":", 1)[1]), force=True)
        except Exception:
            products_ui(cid, 0, force=True)
    elif data == "noop":
        return
    elif data.startswith("product:"):
        show_product(cid, data.split(":", 1)[1], 1)

    elif data.startswith("buybal:"):
        parts = data.split(":")
        key = parts[1]
        qty = int(parts[2]) if len(parts) > 2 else 1
        clear_state(cid)
        buy_balance(cid, key, qty)

    elif data.startswith("buydirect:"):
        parts = data.split(":")
        key = parts[1]
        qty = int(parts[2]) if len(parts) > 2 else 1
        buy_direct(cid, key, qty)
    elif data.startswith("buy:"):
        # Backward compatibility with older buttons.
        buy_balance(cid, data.split(":", 1)[1], 1)
    elif data in {"balance", "wallet"}:
        wallet_menu(cid)
    elif data.startswith("quicktopup:"):
        try:
            amount = Decimal(data.split(":", 1)[1])
            clear_state(cid)
            create_topup(cid, amount)
        except Exception as e:
            print("Quick top-up error:", e)
            send(cid, "❌ Could not create the payment invoice. Please try again.")

    elif data == "topup":
        topup_start(cid)
    elif data == "cancel_topup":
        clear_state(cid)
        send(cid, "✅ Payment cancelled.")
    elif data == "support":
        support_ui(cid)
    elif data == "orders":
        show_orders(cid)
    elif data == "transactions":
        show_transactions(cid)
    elif data == "admin":
        admin_panel(cid)
    elif data == "adm:stats":
        admin_stats(cid)
    elif data == "adm:users":
        admin_users(cid)
    elif data == "adm:orders":
        admin_orders(cid)
    elif data == "adm:pending":
        admin_pending(cid)
    elif data == "adm:transactions":
        admin_transactions(cid)
    elif data == "adm:review":
        admin_review(cid)
    elif data == "adm:suppliers":
        admin_suppliers(cid)
    elif data.startswith("adm:supplier_toggle:"):
        supplier = data.split(":", 2)[2].upper()
        if supplier in {"AIVERSE", "ELITE"}:
            set_supplier_enabled(supplier, not supplier_enabled(supplier))
            admin_suppliers(cid)
    elif data == "adm:supplier_test":
        lines = []
        for supplier in ("AIVERSE", "ELITE"):
            if not supplier_enabled(supplier):
                lines.append(f"⏸ {supplier}: OFF")
                continue
            try:
                items = supplier_services(supplier, force=True)
                lines.append(f"✅ {supplier}: {len(items)} products")
            except Exception as e:
                lines.append(f"❌ {supplier}: {str(e)[:120]}")
        send(cid, "🧪 Supplier Test\n\n" + "\n".join(lines))
    elif data == "adm:custom":
        admin_custom_products(cid)
    elif data == "adm:custom_add":
        admin_custom_add_start(cid)
    elif data.startswith("adm:custom_view:"):
        admin_custom_view(cid, data.split(":", 2)[2])
    elif data.startswith("adm:custom_stock:"):
        admin_custom_stock_start(cid, data.split(":", 2)[2])
    elif data.startswith("adm:custom_price:"):
        admin_custom_price_start(cid, data.split(":", 2)[2])
    elif data.startswith("adm:custom_name:"):
        admin_custom_name_start(cid, data.split(":", 2)[2])
    elif data.startswith("adm:custom_validity:"):
        admin_custom_validity_start(cid, data.split(":", 2)[2])
    elif data.startswith("adm:custom_warranty:"):
        admin_custom_warranty_start(cid, data.split(":", 2)[2])
    elif data.startswith("adm:custom_toggle:"):
        key = data.split(":", 2)[2]
        row = _custom_product_row(key)
        if row:
            c = db()
            c.execute(
                """UPDATE custom_products
                   SET enabled=?,updated_at=CURRENT_TIMESTAMP WHERE product_key=?""",
                (0 if int(row["enabled"] or 0) else 1, key),
            )
            c.commit()
            c.close()
        admin_custom_view(cid, key)
    elif data == "adm:broadcast":
        broadcast_prompt(cid)


def message(m: dict) -> None:
    chat = m.get("chat", {}) or {}

    # V8 privacy/UI rule:
    # The bot never responds to customer commands in groups/supergroups.
    # The configured LOG_CHAT_ID group is only an anonymous activity feed.
    if chat.get("type") != "private":
        return

    upsert_user(m)
    cid = str(chat.get("id"))
    text = (m.get("text") or "").strip()

    if is_admin(cid) and do_broadcast(m):
        return

    if text == "/menu":
        clear_state(cid)
        if joined(cid):
            main_menu(cid)
        else:
            join_gate(cid)
        return

    if text == "/start" or text.startswith("/start "):
        payload = text.split(maxsplit=1)[1].strip() if " " in text else ""
        clear_state(cid)
        if not joined(cid):
            join_gate(cid)
            return
        if payload.startswith("product_"):
            return show_product(cid, payload[len("product_"):], 1)
        return main_menu(cid)
    if text == "/admin":
        return admin_panel(cid)
    if text == "/cancel":
        clear_state(cid)
        return send(cid, "✅ Cancelled.")
    if text == "/cancelbroadcast" and is_admin(cid):
        return send(cid, "No active notification mode.")

    # Admin creation/stock/edit flows are private admin workflows and do not
    # depend on the customer membership gate.
    admin_state, admin_data = get_state(cid)
    if is_admin(cid) and admin_state.startswith("ADMIN_"):
        if handle_admin_state(cid, admin_state, admin_data, text):
            return

    if not joined(cid):
        return join_gate(cid)

    if text in {"/balance", "/wallet"}:
        return wallet_menu(cid)
    if text in {"/products", "/shop"}:
        return products_ui(cid)
    if text == "/topup":
        return topup_start(cid)
    if text == "/support":
        return support_ui(cid)
    if text == "/orders":
        return show_orders(cid)
    if text == "/transactions":
        return show_transactions(cid)

    if text.startswith("/order "):
        parts = text.split(maxsplit=1)
        return show_order(cid, parts[1].strip().upper())

    state, state_data = get_state(cid)

    if state == "AWAIT_TOPUP_TX" and text and not text.startswith("/"):
        ref = state_data.get("ref")
        if not ref:
            clear_state(cid)
            return send(cid, "❌ Payment session expired. Please create a new invoice.")
        return verify_topup(cid, ref, text)

    if state == "PRODUCT_SELECTED" and text and not text.startswith("/"):
        token = str(state_data.get("product_key") or "")

        if text.isdigit():
            try:
                requested_qty = int(text)
                if requested_qty <= 0:
                    raise ValueError

                x = service(token)
                if not x:
                    clear_state(cid)
                    return send(cid, "❌ Product is no longer available.")

                qty = _safe_qty(x, requested_qty)
                key = str(x.get("product_key") or token)
                body, kb = _product_card(cid, x, key, qty)

                # Keep the chat clean: remove the typed quantity message when possible.
                try:
                    delete(cid, m.get("message_id"))
                except Exception:
                    pass

                mid = state_data.get("message_id")
                if mid:
                    try:
                        edit(cid, int(mid), body, kb)
                        set_state(
                            cid,
                            "PRODUCT_SELECTED",
                            {
                                "product_key": key,
                                "quantity": qty,
                                "message_id": int(mid),
                            },
                        )
                        return
                    except Exception as e:
                        print("Product quantity edit warning:", e)

                # Fallback only if the original card cannot be edited.
                result = send(cid, body, kb)
                new_mid = None
                try:
                    new_mid = int(result.get("result", {}).get("message_id"))
                except Exception:
                    new_mid = None
                set_state(
                    cid,
                    "PRODUCT_SELECTED",
                    {
                        "product_key": key,
                        "quantity": qty,
                        "message_id": new_mid,
                    },
                )
                return

            except Exception:
                return

    if text.startswith("/verifytop "):
        parts = text.split()
        if len(parts) >= 3:
            return verify_topup(cid, parts[1].upper(), parts[2])
        return send(cid, "❌ Format: /verifytop TOP-XXXXXXXXXX TRANSACTION_ID")

    if text.startswith("/verify "):
        parts = text.split()
        if len(parts) >= 3:
            return verify_direct(cid, parts[1].upper(), parts[2])
        if len(parts) == 2:
            # Compatibility with the old PayHub bot: /verify TXID
            return verify_direct_legacy(cid, parts[1])
        return send(cid, "❌ Format: /verify ORD-XXXXXXXXXX TRANSACTION_ID")
    if text == "/verify":
        return send(cid, "❌ Use: /verify ORD-XXXXXXXXXX TRANSACTION_ID")

    state, state_data = get_state(cid)
    if state == "AWAIT_TOPUP_AMOUNT" and text and not text.startswith("/"):
        try:
            amount = money(text)
            if amount <= 0:
                raise ValueError("non-positive")
            return create_topup(cid, amount)
        except Exception:
            return send(cid, "❌ Enter a valid amount, for example 0.10, 1, or 10.50. Cancel: /cancel")

    send(cid, "Use /start or /menu to open the main menu.")


def main() -> None:
    init_db()
    configure_telegram_ui()
    print("🤖 Digital shop bot V18 started — Railway Checked | Payment/Admin Fixes")
    threading.Thread(target=start_webhook, daemon=True).start()

    offset: Optional[int] = None
    while True:
        try:
            params: Dict[str, Any] = {"timeout": 30}
            if offset is not None:
                params["offset"] = offset
            r = HTTP.get(f"{TG}/getUpdates", params=params, timeout=40)
            r.raise_for_status()
            d = r.json()
            if not d.get("ok", True):
                raise RuntimeError(d.get("description", "Telegram getUpdates failed"))
            for u in d.get("result", []):
                offset = int(u["update_id"]) + 1
                if "callback_query" in u:
                    callback(u["callback_query"])
                elif "message" in u:
                    message(u["message"])
        except KeyboardInterrupt:
            print("Bot stopped.")
            break
        except Exception as e:
            print("Loop error:", e)
            time.sleep(3)


if __name__ == "__main__":
    main()
