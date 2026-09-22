#!/usr/bin/env python3
"""
Bot de surveillance Pokémon / One Piece TCG — V8 prix +10%.

Format products.txt:
    Nom | URL | prix_normal

Le bot applique automatiquement PRICE_TOLERANCE_PCT (10 % par défaut).
Exemple : prix normal 59,99 € -> alerte seulement jusqu'à 65,99 €.

Aucune commande ni achat automatique n'est effectué.
"""

import argparse
import http.client
import json
import os
import random
import re
import sys
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import zlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse

try:
    import brotli
    HAS_BROTLI = True
except ImportError:
    HAS_BROTLI = False

# ---------------------------------------------------------------------------
# CONFIG
# ---------------------------------------------------------------------------

NTFY_TOPIC = (os.environ.get("NTFY_TOPIC") or "CHANGE-MOI-pokestock-secret-123").strip()
TOPIC_UNSET = NTFY_TOPIC.startswith("CHANGE-MOI")

PRICE_FILTER_ENABLED = os.environ.get("PRICE_FILTER_ENABLED", "1") != "0"
PRICE_REQUIRED = os.environ.get("PRICE_REQUIRED", "1") != "0"
PRICE_TOLERANCE_PCT = float(os.environ.get("PRICE_TOLERANCE_PCT", "10"))
ALERT_ON_PREORDER = os.environ.get("ALERT_ON_PREORDER", "1") != "0"

# Scheduler adaptatif
DEFAULT_INTERVAL = int(os.environ.get("DEFAULT_INTERVAL", "60"))
PRIORITY_INTERVAL = int(os.environ.get("PRIORITY_INTERVAL", "20"))
MIN_INTERVAL = int(os.environ.get("MIN_INTERVAL", "15"))
MAX_INTERVAL = int(os.environ.get("MAX_INTERVAL", "900"))
COOLDOWN_429 = int(os.environ.get("COOLDOWN_429", "120"))
COOLDOWN_403 = int(os.environ.get("COOLDOWN_403", "300"))

REQUEST_TIMEOUT = int(os.environ.get("REQUEST_TIMEOUT", "15"))
FETCH_RETRIES = int(os.environ.get("FETCH_RETRIES", "2"))
MAX_PAGE_BYTES = int(os.environ.get("MAX_PAGE_BYTES", "3000000"))
HOST_DELAY_MIN = float(os.environ.get("HOST_DELAY_MIN", "1.2"))
HOST_DELAY_MAX = float(os.environ.get("HOST_DELAY_MAX", "3.0"))
MAX_WORKERS = int(os.environ.get("MAX_WORKERS", "6"))
RUN_DEADLINE = int(os.environ.get("RUN_DEADLINE", "200"))

WEAK_CONFIRMATIONS = int(os.environ.get("WEAK_CONFIRMATIONS", "2"))
HEARTBEAT_EVERY_HOURS = int(os.environ.get("HEARTBEAT_EVERY_HOURS", "24"))
PROBLEM_ALERT_MINUTES = int(os.environ.get("PROBLEM_ALERT_MINUTES", "30"))
ALERT_COOLDOWN_HOURS = int(os.environ.get("ALERT_COOLDOWN_HOURS", "6"))

BASE_DIR = Path(__file__).resolve().parent
PRODUCTS_FILE = BASE_DIR / "products.txt"
STATE_FILE = BASE_DIR / "stock_state.json"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/128.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,"
              "image/avif,image/webp,image/apng,*/*;q=0.8",
    "Accept-Language": "fr-FR,fr;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept-Encoding": "gzip, deflate, br" if HAS_BROTLI else "gzip, deflate",
    "Sec-Ch-Ua": '"Chromium";v="128", "Not=A?Brand";v="24", "Google Chrome";v="128"',
    "Sec-Ch-Ua-Mobile": "?0",
    "Sec-Ch-Ua-Platform": '"Windows"',
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Upgrade-Insecure-Requests": "1",
}

TRANSIENT_HTTP = {408, 425, 429, 500, 502, 503, 504}

# ---------------------------------------------------------------------------
# STOCK DETECTION
# ---------------------------------------------------------------------------

IN_KEYS = {"instock", "limitedavailability", "onlineonly", "instoreonly",
           "availablefororder", "true"}
PRE_KEYS = {"preorder", "presale", "backorder"}
OUT_KEYS = {"outofstock", "soldout", "discontinued", "oos", "false"}

SCHEMA_RE = re.compile(
    r'(?:schema\.org/|"availability"\s*:\s*")'
    r"(InStock|LimitedAvailability|OnlineOnly|InStoreOnly|"
    r"PreOrder|PreSale|BackOrder|OutOfStock|SoldOut|Discontinued)",
    re.I,
)
OG_RES = [
    re.compile(
        r"""(?:product|og):availability["']\s+content=["']([^"']+)["']""",
        re.I,
    ),
    re.compile(
        r"""content=["']([^"']+)["']\s+(?:property|name)=["'](?:product|og):availability["']""",
        re.I,
    ),
]
LD_RE = re.compile(
    r"""<script[^>]+type=["']application/ld\+json["'][^>]*>(.*?)</script>""",
    re.I | re.S,
)
NEXT_DATA_RE = re.compile(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', re.I | re.S)

OUT_WORDS = [
    "épuisé", "epuise", "rupture de stock", "out of stock", "sold out",
    "indisponible", "plus disponible", "victime de son succès",
]
IN_WORDS = [
    "ajouter au panier", "add to cart", "ajouter à la commande",
    "acheter maintenant", "commander",
]
PRE_WORDS = ["précommande", "precommande", "pre-order", "preorder"]
BLOCK_WORDS = [
    "captcha", "access denied", "just a moment", "datadome",
    "verify you are human", "unusual traffic", "vérification de sécurité",
    "robot check", "cf-chl",
]

def _norm(value) -> str:
    return re.sub(r"[^a-z0-9]", "", str(value).lower().rsplit("/", 1)[-1])

def _walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from _walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk(value)

def _is_product(node: dict) -> bool:
    t = node.get("@type")
    types = t if isinstance(t, list) else [t]
    return any(
        isinstance(x, str) and x.lower() in
        ("product", "productgroup", "individualproduct")
        for x in types
    )

def _ld_nodes(html: str):
    for match in LD_RE.finditer(html):
        try:
            yield json.loads(match.group(1).strip())
        except (ValueError, TypeError):
            continue

def _ld_availability(html: str) -> list:
    for data in _ld_nodes(html):
        for node in _walk(data):
            if isinstance(node, dict) and _is_product(node):
                keys = []
                for sub in _walk([node.get("offers"), node.get("hasVariant")]):
                    if isinstance(sub, dict) and isinstance(sub.get("availability"), str):
                        keys.append(_norm(sub["availability"]))
                if keys:
                    return keys
    return []

def _next_data_availability(html: str) -> list:
    match = NEXT_DATA_RE.search(html)
    if not match:
        return []
    try:
        data = json.loads(match.group(1))
    except (ValueError, TypeError):
        return []

    results = []
    for node in _walk(data):
        if not isinstance(node, dict):
            continue
        if isinstance(node.get("inStock"), bool):
            results.append("instock" if node["inStock"] else "outofstock")
        elif isinstance(node.get("stockQuantity"), (int, float)):
            results.append("instock" if node["stockQuantity"] > 0 else "outofstock")
        elif isinstance(node.get("isAvailable"), bool):
            results.append("instock" if node["isAvailable"] else "outofstock")
        elif isinstance(node.get("availability"), str):
            results.append(_norm(node["availability"]))
    return results

def _decide(keys):
    kinds = set()
    for key in keys:
        if key in IN_KEYS:
            kinds.add("in")
        elif key in PRE_KEYS:
            kinds.add("preorder")
        elif key in OUT_KEYS:
            kinds.add("out")
    for status in ("in", "preorder", "out"):
        if status in kinds:
            return status, kinds
    return None, kinds

def classify(html: str):
    status, _ = _decide(_ld_availability(html))
    if status:
        return status, "schema"

    status, _ = _decide(_next_data_availability(html))
    if status:
        return status, "nextdata"

    status, kinds = _decide([_norm(x) for x in SCHEMA_RE.findall(html)])
    if status:
        return status, "schema" if len(kinds) <= 1 else "keywords"

    og = [_norm(x) for rx in OG_RES for x in rx.findall(html)]
    status, _ = _decide(og)
    if status:
        return status, "meta"

    low = html.lower()
    if any(word in low for word in OUT_WORDS):
        return "out", "keywords"

    has_in = any(word in low for word in IN_WORDS)
    if has_in and any(word in low for word in PRE_WORDS):
        return "preorder", "keywords"
    if has_in:
        return "in", "keywords"

    if any(word in low for word in BLOCK_WORDS):
        return "blocked", "keywords"

    return "unknown", "keywords"

# ---------------------------------------------------------------------------
# PRICE DETECTION
# ---------------------------------------------------------------------------

PRICE_RE = re.compile(
    r"""(?<![\d.,])(\d{1,4}(?:[ .]\d{3})*(?:[,.]\d{1,2})?)\s*(?:€|EUR)\b""",
    re.I,
)
PRICE_RE_REV = re.compile(
    r"""(?:€|EUR)\s*(\d{1,4}(?:[ .]\d{3})*(?:[,.]\d{1,2})?)(?![\d.,])""",
    re.I,
)

def parse_price(value):
    if isinstance(value, (int, float)) and 0 < float(value) < 100000:
        return round(float(value), 2)
    if not isinstance(value, str):
        return None

    s = value.strip().replace("\xa0", " ")
    s = re.sub(r"\s+", " ", s)

    # Formats français: 59,99 / 59.99 / 1 299,90
    s = re.sub(r"[^\d,.\s]", "", s).strip()
    if not s:
        return None

    if "," in s:
        s = s.replace(" ", "").replace(".", "").replace(",", ".")
    else:
        s = s.replace(" ", "")
        if s.count(".") > 1:
            s = s.replace(".", "")
    try:
        value = float(s)
    except ValueError:
        return None
    if not (0 < value < 100000):
        return None
    return round(value, 2)

def _collect_json_prices(html: str):
    prices = []

    for data in _ld_nodes(html):
        for node in _walk(data):
            if not isinstance(node, dict):
                continue
            if _is_product(node):
                for key in ("price", "lowPrice", "highPrice"):
                    if key in node:
                        p = parse_price(node[key])
                        if p is not None:
                            prices.append(p)
            if "offers" in node and isinstance(node["offers"], (dict, list)):
                for offer in _walk(node["offers"]):
                    if isinstance(offer, dict):
                        for key in ("price", "lowPrice"):
                            if key in offer:
                                p = parse_price(offer[key])
                                if p is not None:
                                    prices.append(p)
    return prices

def _collect_next_prices(html: str):
    match = NEXT_DATA_RE.search(html)
    if not match:
        return []
    try:
        data = json.loads(match.group(1))
    except (ValueError, TypeError):
        return []

    prices = []
    for node in _walk(data):
        if not isinstance(node, dict):
            continue
        for key in ("price", "salePrice", "currentPrice", "sellingPrice"):
            if key in node:
                p = parse_price(node[key])
                if p is not None:
                    prices.append(p)
    return prices

def extract_price(html: str):
    prices = _collect_json_prices(html) + _collect_next_prices(html)

    # Meta tags et attributs de prix.
    for pattern in (
        r"""(?:product:price:amount|price)["']?\s*(?:content|value)=["']([^"']+)["']""",
        r"""(?:content|value)=["']([^"']+)["']\s+(?:property|name)=["'](?:product:price:amount|price)["']""",
    ):
        for raw in re.findall(pattern, html, re.I):
            p = parse_price(raw)
            if p is not None:
                prices.append(p)

    # Repli texte, volontairement conservateur: seulement autour d'un symbole €.
    text = re.sub(r"<script\b[^>]*>.*?</script>", " ", html, flags=re.I | re.S)
    text = re.sub(r"<style\b[^>]*>.*?</style>", " ", text, flags=re.I | re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s+", " ", text)
    for rx in (PRICE_RE, PRICE_RE_REV):
        for raw in rx.findall(text):
            p = parse_price(raw)
            if p is not None:
                prices.append(p)

    if not prices:
        return None

    # Les prix les plus bas sont généralement le prix courant.
    # On évite les montants manifestement accessoires.
    prices = sorted(set(round(p, 2) for p in prices))
    return prices[0]

# ---------------------------------------------------------------------------
# NETWORK
# ---------------------------------------------------------------------------

class FetchError(Exception):
    def __init__(self, message, transient=False, status_code=None):
        super().__init__(message)
        self.transient = transient
        self.status_code = status_code

def _http_message(code: int) -> str:
    messages = {
        403: "HTTP 403 (accès refusé / protection anti-bot probable)",
        404: "HTTP 404 (page introuvable)",
        429: "HTTP 429 (trop de requêtes)",
    }
    return messages.get(code, f"HTTP {code}")

def _fetch_once(url: str) -> str:
    req = urllib.request.Request(url, headers=HEADERS)

    proxy = (
        os.environ.get("HTTPS_PROXY") or os.environ.get("HTTP_PROXY") or
        os.environ.get("https_proxy") or os.environ.get("http_proxy")
    )
    opener = (
        urllib.request.build_opener(
            urllib.request.ProxyHandler({"http": proxy, "https": proxy})
        )
        if proxy else urllib.request.build_opener()
    )

    try:
        with opener.open(req, timeout=REQUEST_TIMEOUT) as response:
            raw = response.read(MAX_PAGE_BYTES)
            encoding = (response.headers.get("Content-Encoding") or "").lower()
            charset = response.headers.get_content_charset() or "utf-8"
    except urllib.error.HTTPError as exc:
        raise FetchError(
            _http_message(exc.code), exc.code in TRANSIENT_HTTP, exc.code
        ) from exc

    if encoding == "gzip":
        raw = zlib.decompressobj(16 + zlib.MAX_WBITS).decompress(raw, MAX_PAGE_BYTES)
    elif encoding == "deflate":
        try:
            raw = zlib.decompressobj().decompress(raw, MAX_PAGE_BYTES)
        except zlib.error:
            raw = zlib.decompressobj(-zlib.MAX_WBITS).decompress(raw, MAX_PAGE_BYTES)
    elif encoding == "br":
        if not HAS_BROTLI:
            raise FetchError("page en Brotli mais module brotli absent")
        raw = brotli.decompress(raw)
    elif encoding not in ("", "identity"):
        raise FetchError(f"encodage non géré: {encoding}")

    try:
        return raw.decode(charset, errors="replace")
    except LookupError:
        return raw.decode("utf-8", errors="replace")

def fetch(url: str):
    last = None
    for attempt in range(FETCH_RETRIES + 1):
        try:
            return _fetch_once(url)
        except FetchError as exc:
            last = exc
        except (urllib.error.URLError, http.client.HTTPException, OSError,
                zlib.error, EOFError) as exc:
            last = FetchError(
                f"réseau ({exc.__class__.__name__})", True
            )

        if not last.transient or attempt >= FETCH_RETRIES:
            raise last
        time.sleep(1.5 * (attempt + 1) + random.random())
    raise last

# ---------------------------------------------------------------------------
# NOTIFICATIONS
# ---------------------------------------------------------------------------

def _header(text: str, limit: int = 200) -> str:
    return " ".join(str(text).split()).encode(
        "latin-1", "replace"
    ).decode("latin-1")[:limit]

def notify(title: str, message: str, url: str = "", priority: str = "5",
           tags: str = "rotating_light") -> bool:
    if TOPIC_UNSET:
        print("  ! NTFY_TOPIC non configuré.")
        return False

    endpoint = "https://ntfy.sh/" + urllib.parse.quote(NTFY_TOPIC, safe="")
    headers = {
        "Title": _header(title),
        "Priority": str(priority),
        "Tags": tags,
    }
    if url:
        headers["Click"] = url

    data = str(message)[:1800].encode("utf-8")

    for attempt in range(3):
        try:
            req = urllib.request.Request(
                endpoint, data=data, headers=headers, method="POST"
            )
            urllib.request.urlopen(req, timeout=15).read()
            print("  -> notification envoyée")
            return True
        except Exception as exc:
            if attempt == 2:
                print(f"  ! notification échouée: {exc}")
            else:
                time.sleep(1.5 * (attempt + 1))
    return False

# ---------------------------------------------------------------------------
# PRODUCTS.TXT
# ---------------------------------------------------------------------------

LINE_RE = re.compile(
    r"^(.+?)\s*\|\s*(https?://\S+)\s*\|\s*([0-9]+(?:[.,][0-9]{1,2})?)\s*$"
)

def load_products():
    try:
        text = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except FileNotFoundError:
        raise RuntimeError("products.txt est introuvable à côté du script.")
    except OSError as exc:
        raise RuntimeError(f"products.txt illisible: {exc}")

    products = []
    seen = set()

    for line_no, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue

        match = LINE_RE.match(line)
        if not match or "..." in match.group(2):
            print(
                f"! ligne {line_no} ignorée: format attendu "
                "'Nom | URL | prix_normal'"
            )
            continue

        name = match.group(1).strip()
        url = match.group(2).strip()
        reference_price = parse_price(match.group(3))

        if reference_price is None:
            print(f"! ligne {line_no} ignorée: prix invalide")
            continue
        if url in seen:
            print(f"! doublon ignoré: {name}")
            continue

        seen.add(url)
        products.append({
            "name": name,
            "url": url,
            "reference_price": reference_price,
        })

    if not products:
        raise RuntimeError("products.txt ne contient aucun produit valide.")
    return products

# ---------------------------------------------------------------------------
# STATE
# ---------------------------------------------------------------------------

def new_entry():
    return {
        "status": None,
        "alerted": False,
        "weak_hits": 0,
        "problem_since": 0,
        "problem_alerted": False,
        "next_check": 0,
        "cooldown_until": 0,
        "last_http_status": None,
        "errors": 0,
        "last_price": None,
    }

def new_state():
    return {
        "products": {},
        "last_heartbeat": 0,
        "last_crash_alert": 0,
        "last_config_alert": 0,
    }

def load_state():
    state = new_state()
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("format inattendu")
    except FileNotFoundError:
        return state
    except Exception as exc:
        print(f"! état illisible ({exc}); nouveau state.")
        return state

    for key in ("last_heartbeat", "last_crash_alert", "last_config_alert"):
        if isinstance(data.get(key), (int, float)):
            state[key] = data[key]

    if isinstance(data.get("products"), dict):
        for url, old in data["products"].items():
            entry = new_entry()
            if isinstance(old, dict):
                entry.update({k: old[k] for k in entry if k in old})
            state["products"][str(url)] = entry

    return state

def save_state(state):
    try:
        payload = json.dumps(
            state, indent=2, ensure_ascii=False, sort_keys=True
        ) + "\n"
        tmp = STATE_FILE.with_name(STATE_FILE.name + ".tmp")
        tmp.write_text(payload, encoding="utf-8")
        os.replace(tmp, STATE_FILE)
    except Exception as exc:
        print(f"! écriture state impossible: {exc}")

# -----------------------------
