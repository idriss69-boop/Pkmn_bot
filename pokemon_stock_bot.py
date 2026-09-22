#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Pokemon / One Piece Stock Bot V4
- Monitoring public product pages only
- Adaptive per-product polling
- Conservative stock detection
- Price filtering to avoid overpriced listings
- ntfy notifications
- No automated cart / checkout

products.txt formats:
    Coffret Pokémon X | https://example.com/product | 59.99
    Coffret One Piece | https://example.com/product | 69,90
    [10s] Produit prioritaire | https://example.com/product | 59.99
    Produit sans plafond | https://example.com/product

The third field is the MAXIMUM ACCEPTED PRICE in EUR.
If PRICE_REQUIRED=True, an alert is sent only when a reliable price is found
and is <= the configured maximum.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import logging
import os
import random
import re
import threading
import time
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional
from urllib.parse import urlparse

import requests

# ---------------- Configuration ----------------

PRODUCTS_FILE = os.getenv("PRODUCTS_FILE", "products.txt")
STATE_FILE = os.getenv("STATE_FILE", "pokemon_stock_state_v4.json")

NTFY_TOPIC = os.getenv("NTFY_TOPIC", "").strip()
NTFY_SERVER = os.getenv("NTFY_SERVER", "https://ntfy.sh").rstrip("/")

CHECK_EVERY = float(os.getenv("CHECK_EVERY", "60"))
FAST_INTERVAL = float(os.getenv("FAST_INTERVAL", "20"))
MIN_INTERVAL = float(os.getenv("MIN_INTERVAL", "10"))
MAX_INTERVAL = float(os.getenv("MAX_INTERVAL", "600"))

HTTP_TIMEOUT = float(os.getenv("HTTP_TIMEOUT", "8"))
MAX_WORKERS_PER_DOMAIN = int(os.getenv("MAX_WORKERS_PER_DOMAIN", "4"))

PRICE_FILTER_ENABLED = os.getenv("PRICE_FILTER_ENABLED", "1") == "1"
PRICE_REQUIRED = os.getenv("PRICE_REQUIRED", "1") == "1"
PRICE_TOLERANCE_PCT = float(os.getenv("PRICE_TOLERANCE_PCT", "0"))
DEFAULT_PRICE_MAX = float(os.getenv("DEFAULT_PRICE_MAX", "0"))

# Once one acceptable listing is found, don't notify repeatedly for the same
# product. Set STOP_AFTER_FIRST_ALERT=1 if you want the whole monitor to stop.
FIRST_ACCEPTABLE_STOCK_ONLY = os.getenv("FIRST_ACCEPTABLE_STOCK_ONLY", "1") == "1"
STOP_AFTER_FIRST_ALERT = os.getenv("STOP_AFTER_FIRST_ALERT", "0") == "1"

USER_AGENT = os.getenv(
    "USER_AGENT",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131 Safari/537.36"
)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
log = logging.getLogger("stockbot")

session = requests.Session()
session.headers.update({
    "User-Agent": USER_AGENT,
    "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
    "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.7",
    "Cache-Control": "no-cache",
})

# ---------------- Models ----------------

@dataclass
class Product:
    name: str
    url: str
    max_price: float = DEFAULT_PRICE_MAX
    interval: float = CHECK_EVERY
    priority: bool = False

@dataclass
class Result:
    ok: bool
    stock: bool = False
    price: Optional[float] = None
    price_source: str = ""
    stock_source: str = ""
    confidence: str = "unknown"
    status: int = 0
    error: str = ""
    blocked: bool = False
    elapsed: float = 0.0

# ---------------- Helpers ----------------

def now_ts() -> float:
    return time.time()

def iso_now() -> str:
    return datetime.now(timezone.utc).isoformat()

def parse_price(raw: Any) -> Optional[float]:
    if raw is None:
        return None
    s = str(raw).strip().replace("\xa0", " ")
    s = re.sub(r"[^\d,.\s]", "", s).strip()
    if not s:
        return None

    # French formats: 59,90 / 1 299,90 / 59.90
    if "," in s:
        s = s.replace(" ", "").replace(".", "").replace(",", ".")
    else:
        s = s.replace(" ", "")
        # Avoid treating a thousands separator as decimal.
        if s.count(".") > 1:
            s = s.replace(".", "")
        elif "." in s:
            left, right = s.split(".", 1)
            if len(right) == 3 and len(left) >= 1:
                s = left + right

    try:
        value = float(s)
        return value if value >= 0 else None
    except ValueError:
        return None

def normalize_max_price(value: float) -> float:
    return max(0.0, float(value))

def effective_max_price(p: Product) -> float:
    max_price = p.max_price if p.max_price > 0 else DEFAULT_PRICE_MAX
    if max_price <= 0:
        return 0.0
    return max_price * (1 + PRICE_TOLERANCE_PCT / 100.0)

def price_acceptable(p: Product, price: Optional[float]) -> bool:
    if not PRICE_FILTER_ENABLED:
        return True
    max_price = effective_max_price(p)
    if max_price <= 0:
        return not PRICE_REQUIRED or price is not None
    if price is None:
        return not PRICE_REQUIRED
    return price <= max_price + 1e-9

def parse_products(path: str) -> list[Product]:
    products: list[Product] = []
    priority_re = re.compile(r"^\[(\d+(?:\.\d+)?)s\]\s*", re.I)

    lines = Path(path).read_text(encoding="utf-8").splitlines()
    for line_no, raw in enumerate(lines, 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue

        interval = CHECK_EVERY
        priority = False

        m = priority_re.match(line)
        if m:
            interval = max(MIN_INTERVAL, float(m.group(1)))
            priority = interval <= FAST_INTERVAL
            line = line[m.end():]
        elif line.startswith("🔥"):
            priority = True
            interval = FAST_INTERVAL
            line = line[1:].strip()

        parts = [x.strip() for x in line.split("|")]
        if len(parts) < 2:
            log.warning("Ligne %s ignorée: %s", line_no, raw)
            continue

        name, url = parts[0], parts[1]
        max_price = DEFAULT_PRICE_MAX
        if len(parts) >= 3 and parts[2]:
            parsed = parse_price(parts[2])
            if parsed is None:
                log.warning("Prix max invalide ligne %s: %s", line_no, parts[2])
            else:
                max_price = parsed

        products.append(Product(
            name=name,
            url=url,
            max_price=normalize_max_price(max_price),
            interval=max(MIN_INTERVAL, interval),
            priority=priority,
        ))
    return products

def load_state() -> dict[str, Any]:
    path = Path(STATE_FILE)
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        log.warning("État illisible, réinitialisation: %s", exc)
        return {}

def save_state(state: dict[str, Any]) -> None:
    path = Path(STATE_FILE)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(path)

# ---------------- Price extraction ----------------

def iter_json_objects(obj: Any):
    if isinstance(obj, dict):
        yield obj
        for value in obj.values():
            yield from iter_json_objects(value)
    elif isinstance(obj, list):
        for value in obj:
            yield from iter_json_objects(value)

def extract_price_from_jsonld(html: str) -> tuple[Optional[float], str]:
    scripts = re.findall(
        r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
        html, re.I | re.S
    )
    for script in scripts:
        try:
            obj = json.loads(script)
        except Exception:
            continue
        for item in iter_json_objects(obj):
            if str(item.get("@type", "")).lower() in {"product", "offer", "aggregateoffer"}:
                for key in ("price", "lowPrice", "highPrice"):
                    price = parse_price(item.get(key))
                    if price is not None and key != "highPrice":
                        return price, f"jsonld:{key}"
                offers = item.get("offers")
                if offers:
                    for offer in iter_json_objects(offers):
                        price = parse_price(offer.get("price"))
                        if price is not None:
                            return price, "jsonld:offers.price"
    return None, ""

def extract_price_from_next_data(html: str) -> tuple[Optional[float], str]:
    m = re.search(
        r'<script[^>]+id=["\']__NEXT_DATA__["\'][^>]*>(.*?)</script>',
        html, re.I | re.S
    )
    if not m:
        return None, ""
    try:
        obj = json.loads(m.group(1))
    except Exception:
        return None, ""

    preferred = {"price", "currentPrice", "salePrice", "sellingPrice"}
    for item in iter_json_objects(obj):
        for key, value in item.items():
            if str(key) in preferred:
                price = parse_price(value)
                if price is not None:
                    return price, f"next:{key}"
    return None, ""

def extract_price_from_meta(html: str) -> tuple[Optional[float], str]:
    patterns = [
        r'<meta[^>]+property=["\']product:price:amount["\'][^>]+content=["\']([^"\']+)',
        r'<meta[^>]+name=["\']product:price:amount["\'][^>]+content=["\']([^"\']+)',
    ]
    for pattern in patterns:
        m = re.search(pattern, html, re.I)
        if m:
            price = parse_price(m.group(1))
            if price is not None:
                return price, "meta:product:price:amount"
    return None, ""

def extract_price_from_visible_text(html: str) -> tuple[Optional[float], str]:
    # Conservative fallback: only accept a unique price-like candidate.
    text = re.sub(r"<script\b[^>]*>.*?</script>", " ", html, flags=re.I | re.S)
    text = re.sub(r"<style\b[^>]*>.*?</style>", " ", text, flags=re.I | re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s+", " ", text)

    matches = re.findall(
        r"(?:prix|price)\s*(?:à partir de|from|de)?\s*:?\s*"
        r"([0-9]{1,4}(?:[ .][0-9]{3})*(?:[,.][0-9]{2})?)\s*€",
        text, re.I
    )
    values = [parse_price(x) for x in matches]
    values = [x for x in values if x is not None]
    if len(values) == 1:
        return values[0], "visible:price"
    return None, ""

def extract_price(html: str) -> tuple[Optional[float], str]:
    for extractor in (
        extract_price_from_jsonld,
        extract_price_from_next_data,
        extract_price_from_meta,
        extract_price_from_visible_text,
    ):
        price, source = extractor(html)
        if price is not None:
            return price, source
    return None, ""

# ---------------- Stock detection ----------------

OUT_WORDS = (
    "rupture", "épuisé", "epuise", "indisponible", "out of stock",
    "sold out", "non disponible", "bientôt disponible"
)
IN_WORDS = (
    "ajouter au panier", "add to cart", "acheter", "buy now",
    "en stock", "disponible", "available"
)

def detect_stock(html: str) -> tuple[bool, str, str]:
    # JSON-LD is the strongest generic signal.
    scripts = re.findall(
        r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
        html, re.I | re.S
    )
    for script in scripts:
        try:
            obj = json.loads(script)
        except Exception:
            continue
        for item in iter_json_objects(obj):
            availability = str(item.get("availability", "")).lower()
            if "instock" in availability:
                return True, "jsonld:InStock", "high"
            if "outofstock" in availability or "soldout" in availability:
                return False, "jsonld:OutOfStock", "high"

    # Common page-data markers.
    low = html.lower()
    if any(x in low for x in ("outofstock", "out_of_stock", "sold-out")):
        # Continue checking explicit positive CTA before deciding.
        if not re.search(r"(ajouter\s+au\s+panier|add\s+to\s+cart|acheter)", low):
            return False, "html:out-of-stock", "medium"

    if re.search(r"(ajouter\s+au\s+panier|add\s+to\s+cart|acheter)", low):
        return True, "html:cart-cta", "medium"

    text = re.sub(r"<[^>]+>", " ", html)
    text = re.sub(r"\s+", " ", text).lower()
    if any(x in text for x in IN_WORDS) and not any(x in text for x in OUT_WORDS):
        return True, "text:availability", "low"

    return False, "unknown", "unknown"

def looks_blocked(status: int, html: str) -> bool:
    low = html.lower()
    markers = (
        "captcha", "cloudflare", "access denied", "verify you are human",
        "unusual traffic", "robot check", "challenge-platform"
    )
    return status in (403, 429, 503) or any(x in low for x in markers)

# ---------------- HTTP check ----------------

def check_product(p: Product) -> Result:
    started = time.monotonic()
    try:
        response = session.get(
            p.url,
            timeout=(3.5, HTTP_TIMEOUT),
            allow_redirects=True,
        )
        elapsed = time.monotonic() - started
        html = response.text
        blocked = looks_blocked(response.status_code, html)

        if response.status_code != 200:
            return Result(
                ok=False, status=response.status_code,
                error=f"HTTP {response.status_code}",
                blocked=blocked, elapsed=elapsed,
            )

        stock, stock_source, confidence = detect_stock(html)
        price, price_source = extract_price(html) if stock or PRICE_FILTER_ENABLED else (None, "")

        return Result(
            ok=True,
            stock=stock,
            price=price,
            price_source=price_source,
            stock_source=stock_source,
            confidence=confidence,
            status=response.status_code,
            blocked=blocked,
            elapsed=elapsed,
        )
    except requests.RequestException as exc:
        return Result(ok=False, error=str(exc), elapsed=time.monotonic() - started)

# ---------------- Notifications ----------------

def notify(title: str, message: str, url: str) -> None:
    if not NTFY_TOPIC:
        log.info("NOTIFICATION | %s | %s | %s", title, message, url)
        return

    endpoint = f"{NTFY_SERVER}/{NTFY_TOPIC}"
    try:
        r = session.post(
            endpoint,
            data=message.encode("utf-8"),
            headers={
                "Title": title,
                "Priority": "max",
                "Click": url,
                "Tags": "package",
            },
            timeout=8,
        )
        r.raise_for_status()
    except requests.RequestException as exc:
        log.warning("Notification ntfy échouée: %s", exc)

# ---------------- Adaptive scheduler ----------------

def domain(url: str) -> str:
    return urlparse(url).netloc.lower()

def initial_state(product: Product) -> dict[str, Any]:
    return {
        "last_stock": False,
        "last_price": None,
        "last_check": 0,
        "next_check": 0,
        "error_count": 0,
        "cooldown_until": 0,
        "last_http_status": 0,
        "first_acceptable_alerted": False,
    }

def schedule_next(s: dict[str, Any], p: Product, result: Result) -> None:
    base = p.interval
    if result.status == 429:
        delay = 120.0
    elif result.status == 403 or result.blocked:
        delay = 300.0
    elif not result.ok:
        errors = min(8, int(s.get("error_count", 0)))
        delay = min(MAX_INTERVAL, base * (2 ** errors))
    elif result.stock and price_acceptable(p, result.price):
        delay = min(FAST_INTERVAL, base)
    else:
        delay = base

    jitter = random.uniform(0, max(1.0, delay * 0.10))
    s["next_check"] = now_ts() + delay + jitter

# ---------------- Main loop ----------------

def main_once(products: list[Product], state: dict[str, Any]) -> bool:
    stop_requested = False

    groups: dict[str, list[Product]] = {}
    for p in products:
        groups.setdefault(domain(p.url), []).append(p)

    due: list[Product] = []
    now = now_ts()
    for p in products:
        key = p.url
        s = state.setdefault(key, initial_state(p))
        if s.get("next_check", 0) <= now and s.get("cooldown_until", 0) <= now:
            due.append(p)

    if not due:
        return False

    def worker(p: Product):
        return p, check_product(p)

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS_PER_DOMAIN * max(1, len(groups))) as pool:
        futures = [pool.submit(worker, p) for p in due]
        for fut in concurrent.futures.as_completed(futures):
            p, result = fut.result()
            s = state.setdefault(p.url, initial_state(p))
            previous_stock = bool(s.get("last_stock", False))
            previous_price = s.get("last_price")
            s["last_check"] = now_ts()
            s["last_http_status"] = result.status

            if not result.ok:
                s["error_count"] = int(s.get("error_count", 0)) + 1
            else:
                s["error_count"] = 0

            if result.status == 429:
                s["cooldown_until"] = now_ts() + 120
            elif result.status == 403 or result.blocked:
                s["cooldown_until"] = now_ts() + 300
            else:
                s["cooldown_until"] = 0

            acceptable = result.stock and price_acceptable(p, result.price)

            # Important: stock without an acceptable/known price is NOT an alert.
            if result.stock and PRICE_FILTER_ENABLED and not acceptable:
                if result.price is None:
                    log.info("%s | stock détecté mais prix inconnu -> aucune alerte", p.name)
                else:
                    log.info(
                        "%s | stock à %.2f € > plafond %.2f € -> aucune alerte",
                        p.name, result.price, effective_max_price(p)
                    )

            should_alert = (
                acceptable
                and not s.get("first_acceptable_alerted", False)
                and (not previous_stock or not previous_price or
                     (result.price is not None and result.price != previous_price))
            )

            if should_alert:
                s["first_acceptable_alerted"] = True
                max_price = effective_max_price(p)
                price_text = f"{result.price:.2f} €" if result.price is not None else "prix accepté"
                limit_text = f" (plafond {max_price:.2f} €)" if max_price > 0 else ""
                notify(
                    f"🎯 Stock OK: {p.name}",
                    f"{p.name}\nPrix: {price_text}{limit_text}\n"
                    f"Confiance stock: {result.confidence}\n"
                    f"Détection: {result.stock_source}\n"
                    f"Prix via: {result.price_source or 'n/a'}\n"
                    f"Détecté: {iso_now()}",
                    p.url,
                )
                log.info("ALERTE ACCEPTABLE | %s | %.2f €", p.name, result.price or -1)
                if STOP_AFTER_FIRST_ALERT:
                    stop_requested = True

            # Allow a new alert after the product has returned to unavailable state,
            # but FIRST_ACCEPTABLE_STOCK_ONLY prevents repeated alerts for the same
            # first acceptable discovery.
            s["last_stock"] = result.stock
            s["last_price"] = result.price
            s["last_stock_source"] = result.stock_source
            s["last_price_source"] = result.price_source
            s["last_confidence"] = result.confidence
            s["last_error"] = result.error
            schedule_next(s, p, result)

    save_state(state)
    return stop_requested

def run(products: list[Product], state: dict[str, Any], once: bool = False) -> None:
    log.info(
        "V4 lancé | %d produit(s) | filtre prix=%s | prix obligatoire=%s",
        len(products), PRICE_FILTER_ENABLED, PRICE_REQUIRED
    )
    while True:
        stop = main_once(products, state)
        if stop:
            log.info("STOP_AFTER_FIRST_ALERT activé.")
            return
        if once:
            return

        now = now_ts()
        next_times = [
            float(state.get(p.url, {}).get(
