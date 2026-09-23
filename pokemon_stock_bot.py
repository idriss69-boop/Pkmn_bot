#!/usr/bin/env python3
"""
Bot de surveillance Pokémon / One Piece TCG — V14 prix + stock magasin Lyon.
Version corrigée : élimination stricte des fausses alertes sur les ruptures de stock.
"""

import argparse
import html as html_lib
import http.client
import json
import os
import random
import re
import sys
import time
import traceback
import unicodedata
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

# Stock physique / retrait magasin — zone Lyon métropole.
PHYSICAL_STOCK_ENABLED = os.environ.get("PHYSICAL_STOCK_ENABLED", "1") != "0"
PHYSICAL_ALERT_ENABLED = os.environ.get("PHYSICAL_ALERT_ENABLED", "1") != "0"
PHYSICAL_SCAN_EVERY = int(os.environ.get("PHYSICAL_SCAN_EVERY", "120"))
PHYSICAL_ALERT_COOLDOWN = int(os.environ.get("PHYSICAL_ALERT_COOLDOWN", "600"))
PHYSICAL_STORE_RADIUS_LABEL = os.environ.get("PHYSICAL_STORE_RADIUS_LABEL", "Lyon métropole")

LYON_STORE_NAMES = tuple(x.strip() for x in os.environ.get(
    "LYON_STORE_NAMES",
    "Fnac Lyon Bellecour|Fnac Lyon Part-Dieu|Fnac Lyon - Gare Part-Dieu|"
    "Carrefour Lyon Part Dieu|Carrefour Lyon Confluence|Carrefour Market Lyon Frères Lumière|Carrefour Vénissieux|"
    "Auchan Supermarché Lyon Gerland|Auchan Supermarché Lyon Félix Faure|Auchan Supermarché Garibaldi - Lyon|Auchan Supermarché City Lyon Université|"
    "King Jouet Lyon Grolée|King Dultes Lyon Part-Dieu|King Jouet Boutique Lyon 4ème|King Jouet Orchestra Lyon/Carré de Soie|King Jouet Caluire|King Jouet Givors|"
    "Smyths Toys Bron|JouéClub Lyon Confluence|La Grande Récré LYON La Part Dieu|"
    "Micromania - Zing LYON CENTRE VILLE|Micromania - Zing LYON PART DIEU|Micromania - Zing LYON GRENETTE"
).split("|" ) if x.strip())

# Scheduler adaptatif
DEFAULT_INTERVAL = int(os.environ.get("DEFAULT_INTERVAL", "60"))
PRIORITY_INTERVAL = int(os.environ.get("PRIORITY_INTERVAL", "15"))
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
DISCOVERY_FILE = BASE_DIR / "discovered_products.txt"
AUTO_ADD_DISCOVERED = os.environ.get("AUTO_ADD_DISCOVERED", "1") != "0"
DISCOVERY_ENABLED = os.environ.get("DISCOVERY_ENABLED", "1") != "0"
DISCOVERY_MAX_PER_HOST = int(os.environ.get("DISCOVERY_MAX_PER_HOST", "12"))
DISCOVERY_TIMEOUT = int(os.environ.get("DISCOVERY_TIMEOUT", "12"))
DISCOVERY_EVERY = int(os.environ.get("DISCOVERY_EVERY", "180"))
SEARCH_DISCOVERY_ENABLED = os.environ.get("SEARCH_DISCOVERY_ENABLED", "1") != "0"
SEARCH_ENGINE = os.environ.get("SEARCH_ENGINE", "both").lower()
SEARCH_RESULTS_PER_QUERY = int(os.environ.get("SEARCH_RESULTS_PER_QUERY", "8"))
SEARCH_QUERIES_PER_HOST = int(os.environ.get("SEARCH_QUERIES_PER_HOST", "4"))
SEARCH_TIMEOUT = int(os.environ.get("SEARCH_TIMEOUT", "12"))
AUTO_REFRESH_PRICES = os.environ.get("AUTO_REFRESH_PRICES", "1") != "0"
PRICE_REFRESH_HOURS = float(os.environ.get("PRICE_REFRESH_HOURS", "12"))

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


def is_relevant_pokemon_candidate(title: str, url: str = "") -> bool:
    haystack = f"{title} {url}".lower()
    pokemon = any(
        x in haystack
        for x in (
            "pokemon", "pokémon", "pokemon tcg", "pokémon tcg",
            "pokemon jcc", "pokémon jcc", "pokemon trading card game",
            "pokemon card game",
        )
    )
    product_term = (
        "etb" in haystack
        or "coffret" in haystack
        or "bundle" in haystack
        or "booster" in haystack
        or "display" in haystack
        or "booster box" in haystack
        or "boîte de boosters" in haystack
        or "box" in haystack
        or "pack" in haystack
        or "tripack" in haystack
        or "tri-pack" in haystack
        or "duopack" in haystack
        or "duo pack" in haystack
        or "duo-pack" in haystack
        or "premium collection" in haystack
        or "collection" in haystack
        or "ultra premium collection" in haystack
        or re.search(r"\bupc\b", haystack) is not None
        or "tin" in haystack
        or "mini tin" in haystack
        or "blister" in haystack
        or "deck" in haystack
        or "starter deck" in haystack
        or "deck box" in haystack
        or "deck de combat" in haystack
    )
    return pokemon and product_term


def is_relevant_onepiece_candidate(title: str, url: str = "") -> bool:
    haystack = f"{title} {url}".lower()
    one_piece = any(x in haystack for x in ("one piece", "onepiece", "one-piece"))
    product_term = (
        re.search(r"\bop\s*-?\s*17\b", haystack) is not None
        or re.search(r"\bop\s*-?\s*18\b", haystack) is not None
        or "the dominance of god" in haystack
        or "dominance of god" in haystack
        or "duo pack" in haystack
        or "duo-pack" in haystack
        or "double pack" in haystack
        or "double-pack" in haystack
        or "booster" in haystack
        or "display" in haystack
        or "booster box" in haystack
    )
    return one_piece and product_term

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

    for pattern in (
        r"""(?:product:price:amount|price)["']?\s*(?:content|value)=["']([^"']+)["']""",
        r"""(?:content|value)=["']([^"']+)["']\s+(?:property|name)=["'](?:product:price:amount|price)["']""",
    ):
        for raw in re.findall(pattern, html, re.I):
            p = parse_price(raw)
            if p is not None:
                prices.append(p)

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
        if line.lower().replace(" ", "") in {"nom|url|prix_normal", "nom|url|prixnormal"}:
            continue
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
        "physical_status": None,
        "physical_stores": [],
        "physical_checked_at": 0,
        "physical_last_alert": 0,
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

# ---------------------------------------------------------------------------
# CHECK / PRICE POLICY
# ---------------------------------------------------------------------------

def accepted_price(reference_price: float) -> float:
    return round(reference_price * (1 + PRICE_TOLERANCE_PCT / 100.0), 2)

def _physical_status_from_html(html: str, retailer: str = "") -> tuple[str | None, list[str]]:
    if not html:
        return None, []

    def norm_text(value: str) -> str:
        value = html_lib.unescape(str(value)).lower()
        value = unicodedata.normalize("NFKD", value)
        value = "".join(c for c in value if not unicodedata.combining(c))
        return re.sub(r"\s+", " ", value).strip()

    low = norm_text(html)

    explicit_in = (
        "en stock en magasin", "stock en magasin", "disponible en magasin",
        "disponible dans votre magasin", "disponible dans ce magasin",
        "disponible dans le magasin", "en rayon", "retrait 1h en magasin",
        "retrait 1h gratuit", "retrait sous 2h", "retrait en 2h",
        "disponible pour retrait", "disponible au retrait",
        "disponible a la collecte", "available to collect",
    )
    explicit_out = (
        "indisponible en magasin", "non disponible en magasin",
        "aucun magasin disponible", "pas disponible en magasin",
        "indisponible dans ce magasin", "indisponible dans votre magasin",
    )
    has_out = any(x in low for x in explicit_out)
    positive_phrases = tuple(x for x in explicit_in if x not in (
        "disponible en magasin", "disponible dans votre magasin",
        "disponible dans ce magasin", "disponible dans le magasin",
    ))
    has_in = any(x in low for x in positive_phrases)
    if re.search(r"(?<!in)disponible en magasin", low):
        has_in = True
    if re.search(r"(?<!in)disponible (?:dans votre|dans ce|dans le) magasin", low):
        has_in = True
    if has_out and not any(x in low for x in positive_phrases):
        has_in = False

    aliases = {
        "Fnac Lyon Bellecour": ("fnac lyon bellecour", "fnac bellecour", "fnac lyon 2"),
        "Fnac Lyon Part-Dieu": ("fnac lyon part-dieu", "fnac part-dieu", "fnac lyon part dieu"),
        "Fnac Lyon - Gare Part-Dieu": ("fnac lyon - gare part-dieu", "fnac gare part-dieu"),
        "Carrefour Lyon Part Dieu": ("carrefour lyon part dieu", "carrefour part dieu"),
        "Carrefour Lyon Confluence": ("carrefour lyon confluence", "carrefour confluence"),
        "Carrefour Market Lyon Frères Lumière": ("carrefour market lyon freres lumiere", "carrefour freres lumiere"),
        "Carrefour Vénissieux": ("carrefour venissieux",),
        "Auchan Supermarché Lyon Gerland": ("auchan supermarche lyon gerland", "auchan lyon gerland"),
        "Auchan Supermarché Lyon Félix Faure": ("auchan supermarche lyon felix faure", "auchan lyon felix faure"),
        "Auchan Supermarché Garibaldi - Lyon": ("auchan supermarche garibaldi - lyon", "auchan garibaldi"),
        "Auchan Supermarché City Lyon Université": ("auchan supermarche city lyon universite", "auchan lyon universite"),
        "King Jouet Lyon Grolée": ("king jouet lyon grolee", "king jouet lyon grolée"),
        "King Dultes Lyon Part-Dieu": ("king dultes part dieu",),
        "King Jouet Boutique Lyon 4ème": ("king jouet boutique lyon 4eme",),
        "King Jouet Orchestra Lyon/Carré de Soie": ("king jouet carre de soie", "king jouet vaulx-en-velin"),
        "King Jouet Caluire": ("king jouet caluire",),
        "King Jouet Givors": ("king jouet givors",),
        "Smyths Toys Bron": ("smyths toys bron",),
        "JouéClub Lyon Confluence": ("joueclub lyon confluence",),
        "La Grande Récré LYON La Part Dieu": ("la grande recre la part dieu",),
        "Micromania - Zing LYON CENTRE VILLE": ("micromania lyon centre ville",),
        "Micromania - Zing LYON PART DIEU": ("micromania lyon part dieu",),
        "Micromania - Zing LYON GRENETTE": ("micromania lyon grenette",),
    }

    stores = []
    try:
        blobs = []
        m = NEXT_DATA_RE.search(html)
        if m:
            blobs.append(json.loads(m.group(1)))
        for data in _ld_nodes(html):
            blobs.append(data)

        for data in blobs:
            for node in _walk(data):
                if not isinstance(node, dict):
                    continue
                flat = norm_text(" ".join(str(v) for v in node.values() if isinstance(v, (str, int, float, bool))))
                if not flat:
                    continue
                for store, variants in aliases.items():
                    if any(v in flat for v in variants):
                        available_true = False
                        for key, value in node.items():
                            k = norm_text(key)
                            if isinstance(value, bool) and value and any(token in k for token in ("stock", "available", "disponib", "in_stock", "pickup", "retrait")):
                                available_true = True
                        if available_true or any(marker in flat for marker in explicit_in):
                            stores.append(store)
                        break
    except Exception:
        pass

    def positive_context(text: str) -> bool:
        if any(x in text for x in explicit_out):
            strong = tuple(x for x in explicit_in if x not in (
                "disponible en magasin", "disponible dans votre magasin",
                "disponible dans ce magasin", "disponible dans le magasin",
            ))
            return any(x in text for x in strong)
        return any(x in text for x in explicit_in)

    for store, variants in aliases.items():
        for variant in variants:
            pos = low.find(variant)
            if pos < 0:
                continue
            context = low[max(0, pos - 1800):min(len(low), pos + 2600)]
            if positive_context(context):
                stores.append(store)
                break

    stores = list(dict.fromkeys(stores))

    if "smythstoys" in retailer.lower() or "smyths" in low:
        strict_stores = []
        strong_smyths = ("en stock en magasin", "stock en magasin", "disponible en magasin", "en rayon", "retrait en 2h")
        for store in stores:
            variants = aliases.get(store, ())
            for variant in variants:
                pos = low.find(variant)
                if pos >= 0:
                    context = low[max(0, pos - 1800):min(len(low), pos + 2600)]
                    if any(x in context for x in strong_smyths) and not any(x in context for x in explicit_out):
                        strict_stores.append(store)
                        break
        stores = list(dict.fromkeys(strict_stores))

    if stores:
        return "in", stores
    if has_out and not has_in:
        return "out", []
    if has_in:
        return "possible", []
    return None, []

def physical_result(product: dict, html: str) -> dict:
    retailer = urlparse(product.get("url", "")).netloc.lower()
    status, stores = _physical_status_from_html(html, retailer)
    return {
        "physical_status": status,
        "physical_stores": stores,
        "physical_checked_at": time.time(),
    }


def _physical_alert_body(result: dict) -> str:
    stores = result.get("physical_stores") or []
    if stores:
        where = "\n".join(f"🟢 {store} : STOCK DÉTECTÉ" for store in stores)
    else:
        where = "🟡 Stock magasin détecté, mais magasin précis non exposé"
    price = result.get("price")
    price_text = f"Prix en ligne : {price:.2f} €" if isinstance(price, (int, float)) else "Prix en ligne : non déterminé"
    return (
        f"🏬 STOCK MAGASIN DÉTECTÉ — {result['name']}\n"
        f"Zone : {PHYSICAL_STORE_RADIUS_LABEL}\n"
        f"{where}\n"
        f"{price_text}\n"
        f"{result['url']}\n\n"
        "Vérification finale conseillée sur la page du magasin avant de te déplacer."
    )


def maybe_notify_physical(state: dict, result: dict):
    if not PHYSICAL_ALERT_ENABLED:
        return
    if result.get("physical_status") != "in":
        return
    entry = state["products"].setdefault(result["url"], new_entry())
    current = tuple(result.get("physical_stores") or [])
    previous = tuple(entry.get("physical_stores") or [])
    now = time.time()
    changed = (not previous) or current != previous or entry.get("physical_status") != "in"
    cooldown_ok = now - float(entry.get("physical_last_alert", 0) or 0) >= PHYSICAL_ALERT_COOLDOWN
    if current and changed and cooldown_ok:
        notify(
            f"🏬 Stock magasin Lyon : {result['name']}",
            _physical_alert_body(result),
            priority="5",
            tags="shopping_cart,department_store",
        )
        entry["physical_last_alert"] = now
    entry["physical_status"] = result.get("physical_status")
    entry["physical_stores"] = list(current)
    entry["physical_checked_at"] = result.get("physical_checked_at", time.time())

def check_one(product: dict) -> dict:
    result = {
        **product,
        "status": None,
        "source": None,
        "price": None,
        "error": None,
        "http_status": None,
        "physical_status": None,
        "physical_stores": [],
        "physical_checked_at": 0,
    }

    try:
        html = fetch(product["url"])
        result["status"], result["source"] = classify(html)

        if PRICE_FILTER_ENABLED:
            result["price"] = extract_price(html)
        if PHYSICAL_STOCK_ENABLED:
            result.update(physical_result(product, html))
    except FetchError as exc:
        result["error"] = str(exc)
        result["http_status"] = exc.status_code
    except Exception as exc:
        result["error"] = (
            f"erreur inattendue ({exc.__class__.__name__}: {str(exc)[:80]})"
        )
    return result

def due(product, entry, now):
    if not entry.get("next_check"):
        return True
    return now >= float(entry.get("next_check", 0))

def schedule_next(entry, result, now):
    status = result.get("status")
    http_status = result.get("http_status")
    errors = int(entry.get("errors", 0))

    if http_status == 429:
        entry["cooldown_until"] = now + COOLDOWN_429
        entry["next_check"] = now + COOLDOWN_429
        return

    if http_status == 403:
        entry["cooldown_until"] = now + COOLDOWN_403
        entry["next_check"] = now + COOLDOWN_403
        return

    if result.get("error"):
        errors += 1
        entry["errors"] = min(errors, 8)
        interval = min(MAX_INTERVAL, DEFAULT_INTERVAL * (2 ** min(errors, 4)))
    else:
        entry["errors"] = 0
        entry["cooldown_until"] = 0

        drop_hay = f"{entry.get('name', '')} {entry.get('url', '')}".lower()
        is_drop = any(term in drop_hay for term in DROP_PRIORITY_TERMS)
        if is_drop:
            interval = DROP_PRIORITY_INTERVAL
        elif status in ("in", "preorder"):
            interval = PRIORITY_INTERVAL
        elif entry.get("alerted"):
            interval = PRIORITY_INTERVAL
        else:
            interval = DEFAULT_INTERVAL

    jitter = random.uniform(-0.10, 0.10) * interval
    interval = max(MIN_INTERVAL, int(interval + jitter))
    entry["next_check"] = now + interval

def process_result(state, result):
    url = result["url"]
    entry = state["products"].setdefault(url, new_entry())
    entry["name"] = result.get("name", entry.get("name", ""))
    entry["url"] = url
    now = time.time()

    if result["error"]:
        if not entry["problem_since"]:
            entry["problem_since"] = now
        minutes = (now - entry["problem_since"]) / 60
        print(f"- {result['name']}: ERREUR {result['error']} [{minutes:.0f} min]")
        schedule_next(entry, result, now)
        return

    if entry["problem_alerted"]:
        notify(
            "Bot Pokémon : site de nouveau lisible",
            result["name"],
            result["url"],
            priority="2",
            tags="white_check_mark",
        )

    entry["problem_since"] = 0
    entry["problem_alerted"] = False
    entry["last_http_status"] = 200
    entry["status"] = result["status"]
    entry["last_price"] = result["price"]

    maybe_notify_physical(state, result)

    labels = {
        "in": "EN STOCK",
        "preorder": "PRÉCOMMANDE",
        "out": "épuisé",
        "blocked": "BLOQUÉ",
        "unknown": "INCONNU",
    }
    label = labels.get(result["status"], result["status"])
    price_txt = (
        f" | prix {result['price']:.2f} €"
        if result["price"] is not None else ""
    )
    print(f"- {result['name']}: {label} [{result['source']}]{price_txt}")

    # =========================================================================
    # CORRECTION CRITIQUE : Empêcher absolument toute alerte si le produit 
    # n'est PAS explicitement en stock ("in") ou en précommande ("preorder").
    # =========================================================================
    is_in_stock = (result["status"] == "in")
    is_preorder = (result["status"] == "preorder" and ALERT_ON_PREORDER)

    if not (is_in_stock or is_preorder):
        # Le produit est épuisé, bloqué, ou inconnu : on réinitialise l'alerte
        entry["alerted"] = False
        entry["weak_hits"] = 0
        schedule_next(entry, result, now)
        return

    # Vérification du filtre prix (uniquement si le produit est dispo/préco)
    price_ok = True
    if PRICE_FILTER_ENABLED:
        if result["price"] is None:
            price_ok = not PRICE_REQUIRED
        else:
            ceiling = accepted_price(result["reference_price"])
            price_ok = result["price"] <= ceiling

            if not price_ok:
                entry["alerted"] = False
                entry["weak_hits"] = 0
                print(
                    f"  -> prix refusé: {result['price']:.2f} € > "
                    f"plafond {ceiling:.2f} €"
                )
                schedule_next(entry, result, now)
                return

    if not price_ok:
        entry["alerted"] = False
        entry["weak_hits"] = 0
        schedule_next(entry, result, now)
        return

    # Détection faible: confirmation sur deux lectures.
    if result["source"] == "keywords":
        entry["weak_hits"] = int(entry.get("weak_hits", 0)) + 1
        if entry["weak_hits"] < WEAK_CONFIRMATIONS:
            print("  ... détection faible, confirmation au prochain passage")
            schedule_next(entry, result, now)
            return

    if not entry["alerted"]:
        ceiling = accepted_price(result["reference_price"])
        price_text = (
            f"Prix détecté : {result['price']:.2f} €\n"
            f"Prix normal : {result['reference_price']:.2f} €\n"
            f"Plafond +{PRICE_TOLERANCE_PCT:g}% : {ceiling:.2f} €"
            if PRICE_FILTER_ENABLED else
            "Filtre prix désactivé."
        )
        title = (
            f"Stock dispo : {result['name']}"
            if result["status"] == "in"
            else f"Précommande : {result['name']}"
        )
        message = (
            f"{result['name']}\n\n"
            f"{price_text}\n\n"
            f"{result['url']}\n\n"
            f"Source stock : {result['source']}"
        )
        if notify(title, message, result["url"], priority="5",
                  tags="rotating_light"):
            entry["alerted"] = True

    schedule_next(entry, result, now)


def run_due(state, products, deadline):
    now = time.time()
    due_products = [
        p for p in products
        if due(p, state["products"].setdefault(p["url"], new_entry()), now)
    ]

    if not due_products:
        return 0, 0, 0

    groups = {}
    for product in due_products:
        host = urlparse(product["url"]).netloc.lower()
        groups.setdefault(host, []).append(product)

    results = []
    def worker(group):
        local = []
        for i, product in enumerate(group):
            if time.monotonic() > deadline:
                break
            if i:
                time.sleep(random.uniform(HOST_DELAY_MIN, HOST_DELAY_MAX))
            local.append(check_one(product))
        return local

    workers = max(1, min(MAX_WORKERS, len(groups)))
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(worker, group) for group in groups.values()]
        for future in as_completed(futures):
            try:
                results.extend(future.result())
            except Exception as exc:
                print(f"! groupe de vérification en erreur: {exc}")

    checked = 0
    available = 0
    errors = 0
    for result in results:
        checked += 1
        if result.get("error"):
            errors += 1
        elif result.get("status") in ("in", "preorder"):
            available += 1
        process_result(state, result)

    return checked, available, errors

def safe_cycle(state, products):
    try:
        started = time.monotonic()
        checked, available, errors = run_due(
            state, products, started + RUN_DEADLINE
        )
        save_state(state)
        if checked:
            print(
                f"[{datetime.now():%H:%M:%S}] "
                f"{checked} vérif(s), {available} dispo(s), "
                f"{errors} erreur(s), {time.monotonic()-started:.1f}s"
            )
    except Exception:
        trace = traceback.format_exc()
        print(trace)
        if time.time() - state.get("last_crash_alert", 0) >= ALERT_COOLDOWN_HOURS * 3600:
            notify(
                "Bot Pokémon : erreur interne",
                trace[-1200:],
                priority="4",
                tags="warning",
            )
            state["last_crash_alert"] = time.time()
        save_state(state)

# ---------------------------------------------------------------------------
# NETTOYAGE AUTOMATIQUE DES ANCIENNES CIBLES
# ---------------------------------------------------------------------------

PURGE_PRODUCT_TERMS = (
    "storm emerald",
    "storm emerald m6",
    "eb-05",
    "eb05",
    "heroines edition vol. 2",
)

def purge_obsolete_products() -> int:
    try:
        current = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        return 0

    kept = []
    removed = 0
    for raw in current.splitlines():
        line = raw.strip()
        m = LINE_RE.match(line) if line and not line.startswith("#") else None
        if not m:
            kept.append(raw)
            continue

        name, url = m.group(1).strip(), m.group(2).strip()
        haystack = f"{name} {url}".lower()
        if any(term in haystack for term in PURGE_PRODUCT_TERMS):
            removed += 1
            print(f"- ancienne cible supprimée de products.txt : {name}")
            continue
        kept.append(raw)

    if removed:
        try:
            PRODUCTS_FILE.write_text("\n".join(kept).rstrip() + "\n", encoding="utf-8")
        except OSError as exc:
            print(f"! purge products.txt impossible: {exc}")
            return 0

    return removed

# ---------------------------------------------------------------------------
# AUTO-DISCOVERY DES NOUVEAUX PRODUITS
# ---------------------------------------------------------------------------

DISCOVERY_KEYWORDS = (
    "pokemon", "pokémon", "one-piece", "onepiece", "one_piece",
    "op-", "op17", "op 17", "op18", "op 18", "eb-", "eb05", "display", "booster",
    "etb", "coffret", "bundle", "blister", "pack", "box",
)

DISCOVERY_WATCH_TERMS = (
    "One Piece Card Game", "One Piece TCG", "ONE PIECE",
    "OP-17", "OP17", "OP 17", "OP-18", "OP18", "OP 18",
    "The Dominance of God", "Dominance of God",
    "30e Anniversaire", "30e anniversaire", "30ème Anniversaire", "30ème anniversaire",
    "30eme Anniversaire", "30eme anniversaire", "30th Anniversary", "30th anniversary",
    "30th-Anniversary", "30th-anniversary", "30th Celebration", "30th celebration",
    "30 ans", "30ans", "30 ans Pokémon", "Pokémon 30 ans",
    "Règne Delta", "Delta Reign", "ME06")

DROP_PRIORITY_TERMS = (
    "op17", "op-17", "op 17", "double pack", "double-pack", "duo pack", "duo-pack",
    "op18", "op-18", "op 18", "the dominance of god", "dominance of god",
    "30e anniversaire", "30ème anniversaire", "30eme anniversaire",
    "30th anniversary", "30th-anniversary", "30th celebration",
    "30 ans", "30ans", "30 ans pokémon", "pokémon 30 ans",
    "règne delta", "règne delta m6", "delta reign", "me06",
)
DROP_PRIORITY_INTERVAL = int(os.environ.get("DROP_PRIORITY_INTERVAL", "10"))
DISCOVERY_IMMEDIATE_CHECK = os.environ.get("DISCOVERY_IMMEDIATE_CHECK", "1") != "0"

def is_drop_priority(product: dict) -> bool:
    hay = f"{product.get('name', '')} {product.get('url', '')}".lower()
    return any(term in hay for term in DROP_PRIORITY_TERMS)


def _product_title(html: str, fallback_url: str) -> str:
    for pat in (
        r'<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)',
        r'<title[^>]*>\s*([^<]+?)\s*</title>',
        r'"name"\s*:\s*"([^"\\]{3,180})"',
    ):
        m = re.search(pat, html, re.I | re.S)
        if m:
            title = re.sub(r"\s+", " ", m.group(1)).strip()
            if title:
                return title[:180]
    return urllib.parse.unquote(urlparse(fallback_url).path.rstrip("/").split("/")[-1]).replace("-", " ")[:180]


def _seller_matches_retailer(seller, retailer: str) -> bool:
    if not seller:
        return False
    low = _norm(seller)
    wanted = _norm(retailer)
    aliases = {
        "fnac": {"fnac", "fnaccom"},
        "carrefour": {"carrefour", "carrefourfr"},
        "auchan": {"auchan", "auchanfr"},
        "cultura": {"cultura", "culturacom"},
        "kingjouet": {"kingjouet", "kingjouetcom"},
        "smythstoys": {"smythstoys", "smythstoyscom"},
        "joueclub": {"joueclub", "joueclubfr"},
        "lagranderecre": {"lagranderecre", "lagranderecrefr"},
        "micromania": {"micromania", "micromaniafr"},
    }
    return low == wanted or low in aliases.get(wanted, {wanted})


def _official_retailer_prices(html: str, retailer: str) -> list[float]:
    prices = []
    structured_offers = False
    for data in _ld_nodes(html):
        for node in _walk(data):
            if not isinstance(node, dict):
                continue
            offers = node.get("offers")
            if isinstance(offers, dict):
                offers = [offers]
            if not isinstance(offers, list):
                continue
            for offer in offers:
                if not isinstance(offer, dict) or offer.get("price") is None:
                    continue
                seller = offer.get("seller")
                seller_name = seller.get("name") if isinstance(seller, dict) else seller if isinstance(seller, str) else None
                if seller_name:
                    structured_offers = True
                    if _seller_matches_retailer(seller_name, retailer):
                        value = parse_price(offer.get("price"))
                        if value is not None and value > 0:
                            prices.append(value)
                else:
                    value = parse_price(offer.get("price"))
                    if value is not None and value > 0:
                        prices.append(value)
    if prices:
        return prices
    if structured_offers:
        return []
    fallback = extract_price(html)
    return [fallback] if fallback is not None and fallback > 0 else []


def _reference_price_from_retailer(html: str, retailer: str):
    prices = _official_retailer_prices(html, retailer)
    if not prices:
        return None
    return min(prices)


def _extract_gtin_candidates(html: str) -> list[str]:
    vals = []
    patterns = [
        r'"(?:gtin13|gtin|ean)"\s*:\s*"?(\d{13})',
        r'\b(\d{13})\b',
    ]
    for pat in patterns:
        for m in re.finditer(pat, html, re.I):
            v = m.group(1)
            if v not in vals:
                vals.append(v)
            if len(vals) >= 5:
                return vals
    return vals

def _candidate_product_queries(name: str, html: str) -> list[str]:
    qs = []
    for ean in _extract_gtin_candidates(html):
        qs.append(ean)
    title = _product_title(html, "")
    if title:
        clean = re.sub(r"^(?:[^|]+\s-\s)+", "", title).strip()
        qs.append('"' + clean[:120] + '"')
    if name:
        clean_name = re.sub(r"^[^|]+\s-\s", "", name).strip()
        if clean_name:
            qs.append('"' + clean_name[:120] + '"')
    return list(dict.fromkeys(qs))

def _find_official_price_for_product(name: str, source_url: str, source_html: str):
    prices = []
    seen_urls = set()
    queries = _candidate_product_queries(name, source_html)
    for domain, (retailer, _families) in DISCOVERY_RETAILERS.items():
        for base_query in queries[:3]:
            query = f'site:{domain} {base_query}'
            for url in _search_engine_urls(query)[:SEARCH_RESULTS_PER_QUERY]:
                parsed = urlparse(url)
                if parsed.netloc.lower().split(":")[0].lstrip("www.") != domain:
                    continue
                clean = url.rstrip("/")
                if clean in seen_urls or any(x in parsed.path.lower() for x in ("/search", "/recherche", "/account", "/login", "/panier", "/cart")):
                    continue
                seen_urls.add(clean)
                try:
                    html = _fetch_once(url)
                except Exception:
                    continue
                title = _product_title(html, url).lower()
                src_title = _product_title(source_html, source_url).lower()
                tokens = [t for t in re.findall(r"[a-z0-9éèêàùûôîïç]+", src_title) if len(t) >= 4]
                overlap = sum(1 for t in set(tokens) if t in title)
                ean_match = bool(set(_extract_gtin_candidates(source_html)) & set(_extract_gtin_candidates(html)))
                if not ean_match and overlap < 3:
                    continue
                price = _reference_price_from_retailer(html, retailer)
                if price is not None:
                    prices.append((price, retailer, clean))
    if not prices:
        return None
    return min(prices, key=lambda x: x[0])

def refresh_existing_reference_prices(products: list[dict]) -> int:
    if not AUTO_REFRESH_PRICES:
        return 0
    changed = 0
    rows = []
    try:
        text = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        return 0
    for raw in text.splitlines():
        line = raw.strip()
        m = LINE_RE.match(line) if line and not line.startswith("#") else None
        if not m:
            rows.append(raw)
            continue
        name, url, old_price = m.group(1).strip(), m.group(2).strip(), parse_price(m.group(3))
        if old_price is None:
            rows.append(raw); continue
        if not re.search(r"pokemon|pokémon|one[ -]?piece|op-\d+|eb-\d+", name + " " + url, re.I):
            rows.append(raw); continue
        try:
            source_html = _fetch_once(url)
            found = _find_official_price_for_product(name, url, source_html)
        except Exception:
            found = None
        if found is None:
            rows.append(raw)
            continue
        new_price, retailer, matched_url = found
        if abs(new_price - old_price) >= 0.01:
            rows.append(f"{name} | {url} | {new_price:.2f}")
            changed += 1
            print(f"~ prix référence mis à jour: {name} : {old_price:.2f} -> {new_price:.2f} ({retailer})")
        else:
            rows.append(raw)
    if changed:
        try:
            PRODUCTS_FILE.write_text("\n".join(rows) + "\n", encoding="utf-8")
        except OSError as exc:
            print(f"! impossible d'écrire les nouveaux prix: {exc}")
            return 0
    return changed

def _append_products_txt(items: list[dict]) -> int:
    if not items:
        return 0
    try:
        current = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        current = ""
    existing_urls = set()
    for line in current.splitlines():
        m = LINE_RE.match(line.strip())
        if m:
            existing_urls.add(m.group(2).rstrip("/"))
    additions = []
    for item in items:
        url = item["url"].rstrip("/")
        price = item.get("reference_price")
        if not url or price is None or url in existing_urls:
            continue
        additions.append(f'{item["name"]} | {url} | {price:.2f}')
        existing_urls.add(url)
    if not additions:
        return 0
    sep = "\n" if current and not current.endswith("\n") else ""
    try:
        PRODUCTS_FILE.write_text(current + sep + "\n# Produits découverts automatiquement — prix enseigne\n" + "\n".join(additions) + "\n", encoding="utf-8")
        return len(additions)
    except OSError as exc:
        print(f"! impossible d'ajouter automatiquement à products.txt: {exc}")
        return 0

DISCOVERY_RETAILERS = {
    "fnac.com": ("Fnac", ("Pokémon", "One Piece")),
    "carrefour.fr": ("Carrefour", ("Pokémon", "One Piece")),
    "auchan.fr": ("Auchan", ("Pokémon", "One Piece")),
    "cultura.com": ("Cultura", ("Pokémon", "One Piece")),
    "king-jouet.com": ("King Jouet", ("Pokémon", "One Piece")),
    "smythstoys.com": ("Smyths Toys", ("Pokémon", "One Piece")),
    "joueclub.fr": ("JouéClub", ("Pokémon", "One Piece")),
    "lagranderecre.fr": ("La Grande Récré", ("Pokémon", "One Piece")),
    "micromania.fr": ("Micromania", ("Pokémon", "One Piece")),
}


def _search_result_urls_google(query: str) -> list[str]:
    url = "https://www.google.com/search?" + urllib.parse.urlencode({
        "q": query, "num": SEARCH_RESULTS_PER_QUERY, "hl": "fr", "gl": "fr",
    })
    try:
        text = _fetch_once(url)
    except Exception:
        return []
    found = []
    for m in re.finditer(r'href=["\'](/url\?q=|)(https?://[^"\'&<>]+)', text, re.I):
        u = html_lib.unescape(m.group(2))
        if u not in found:
            found.append(u)
    for m in re.finditer(r'href=["\']/url\?q=([^&"\']+)', text, re.I):
        u = urllib.parse.unquote(html_lib.unescape(m.group(1)))
        if u.startswith("http") and u not in found:
            found.append(u)
    return found[:SEARCH_RESULTS_PER_QUERY * 2]


def _search_result_urls_bing(query: str) -> list[str]:
    url = "https://www.bing.com/search?" + urllib.parse.urlencode({
        "q": query, "count": SEARCH_RESULTS_PER_QUERY, "setlang": "fr-FR",
    })
    try:
        text = _fetch_once(url)
    except Exception:
        return []
    found = []
    for m in re.finditer(r'<li[^>]*class=["\'][^"\']*b_algo[^"\']*["\'][\s\S]*?<h2[^>]*>\s*<a[^>]+href=["\']([^"\']+)', text, re.I):
        u = html_lib.unescape(m.group(1))
        if u.startswith("http") and u not in found:
            found.append(u)
    return found[:SEARCH_RESULTS_PER_QUERY * 2]


def _search_engine_urls(query: str) -> list[str]:
    urls = []
    engines = []
    if SEARCH_ENGINE in ("google", "both"):
        engines.append(_search_result_urls_google)
    if SEARCH_ENGINE in ("bing", "both"):
        engines.append(_search_result_urls_bing)
    for engine in engines:
        urls.extend(engine(query))
    return list(dict.fromkeys(urls))


def discover_via_search_engines(products: list[dict]) -> list[dict]:
    if not SEARCH_DISCOVERY_ENABLED or not AUTO_ADD_DISCOVERED:
        return []

    known = {p["url"].rstrip("/") for p in products}
    discovered = []

    for domain, (retailer, families) in DISCOVERY_RETAILERS.items():
        queries = [
            f'site:{domain} (pokemon OR pokémon) ("30e Anniversaire" OR "30ème Anniversaire" OR "30eme Anniversaire" OR "30th Anniversary" OR "30th Celebration" OR "30 ans" OR "30ans" OR "Règne Delta" OR "Delta Reign" OR "ME06") (ETB OR coffret OR booster OR display OR pack OR bundle OR collection OR tin OR blister OR deck)',
            f'site:{domain} ("One Piece Card Game" OR "One Piece TCG" OR OP-18 OR OP18 OR "OP 18" OR "The Dominance of God" OR OP-17 OR OP17 OR "OP 17" OR "Double Pack" OR "Duo Pack") (précommande OR acheter OR stock OR display OR booster)',
            f'site:{domain} (pokemon OR pokémon) (ETB OR coffret OR booster OR display OR pack OR bundle OR collection OR tin OR blister OR deck) (précommande OR acheter OR stock OR disponible)',
            f'site:{domain} "{families[0]}" (booster OR display OR coffret OR ETB OR pack OR box)',
            f'site:{domain} "{families[1]}" (booster OR display OR coffret OR ETB OR pack OR box)',
        ]

        for query in queries[:max(SEARCH_QUERIES_PER_HOST + 1, 6)]:
            for url in _search_engine_urls(query):
                parsed = urlparse(url)
                if parsed.netloc.lower().split(":")[0].lstrip("www.") != domain:
                    continue
                clean = url.rstrip("/")
                if clean in known:
                    continue
                path = parsed.path.lower()
                if any(x in path for x in ("/search", "/recherche", "/account", "/login", "/panier", "/cart")):
                    continue
                try:
                    html = _fetch_once(url)
                except Exception:
                    continue
                title = _product_title(html, url)
                is_pokemon = is_relevant_pokemon_candidate(title, url)
                is_onepiece = is_relevant_onepiece_candidate(title, url)
                if not (is_pokemon or is_onepiece):
                    continue

                reference_price = _reference_price_from_retailer(html, retailer)
                if reference_price is None:
                    continue
                status, source = classify(html)
                item = {
                    "name": f"{retailer} - {title}",
                    "url": clean,
                    "reference_price": reference_price,
                    "reference_source": retailer,
                    "price": reference_price,
                    "status": status,
                    "source": source,
                }
                discovered.append(item)
                known.add(clean)

    if not discovered:
        return []

    added = _append_products_txt(discovered)
    if added:
        print(f"+ {added} nouveau(x) produit(s) ajouté(s) automatiquement à products.txt")
    return discovered

def activate_new_discoveries(state: dict, products: list[dict], discovered: list[dict]):
    if not discovered:
        return products
    products[:] = load_products()
    discovered_urls = {x.get("url", "").rstrip("/") for x in discovered}
    for p in products:
        if p["url"].rstrip("/") in discovered_urls:
            entry = state["products"].setdefault(p["url"], new_entry())
            entry["name"] = p.get("name", "")
            entry["url"] = p["url"]
            entry["next_check"] = 0
    if DISCOVERY_IMMEDIATE_CHECK:
        priority = [p for p in products if p["url"].rstrip("/") in discovered_urls and is_drop_priority(p)]
        if priority:
            print(f"⚡ {len(priority)} nouvelle(s) cible(s) DROP : vérification immédiate")
            run_due(state, priority, time.monotonic() + min(RUN_DEADLINE, 60))
            save_state(state)
    return products


def discover_new_products(products: list[dict]) -> list[dict]:
    return []

# ---------------------------------------------------------------------------
# CLI

def main():
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

    parser = argparse.ArgumentParser(
        description="Surveillance de stock Pokémon / One Piece avec filtre prix."
    )
    parser.add_argument("--once", action="store_true",
                        help="vérifie uniquement les produits arrivés à échéance")
    parser.add_argument("--fast", action="store_true",
                        help="surveillance rapide pendant quelques minutes")
    parser.add_argument("--duration", type=int, default=300,
                        help="durée de --fast en secondes")
    parser.add_argument("--interval", type=int, default=20,
                        help="intervalle de base du mode --fast")
    parser.add_argument("--test", action="store_true",
                        help="teste ntfy")
    parser.add_argument("--physical", action="store_true",
                        help="force un scan des fiches pour détecter le stock magasin Lyon")
    args = parser.parse_args()

    if args.test:
        sys.exit(0 if notify(
            "Test bot Pokémon",
            "Les notifications ntfy fonctionnent.",
            priority="3",
            tags="white_check_mark",
        ) else 1)

    purge_obsolete_products()

    if args.physical:
        try:
            products = load_products()
        except RuntimeError as exc:
            print(f"! {exc}")
            sys.exit(2)
        state = load_state()
        for product in products:
            state["products"].setdefault(product["url"], new_entry())["next_check"] = 0
        safe_cycle(state, products)
        return

    try:
        products = load_products()
    except RuntimeError as exc:
        print(f"! {exc}")
        sys.exit(2)

    state = load_state()

    last_price_refresh = state.get("last_price_refresh", 0)
    if AUTO_REFRESH_PRICES and (time.time() - last_price_refresh >= PRICE_REFRESH_HOURS * 3600 or args.once):
        try:
            refresh_existing_reference_prices(products)
            products[:] = load_products()
            state["last_price_refresh"] = time.time()
            save_state(state)
        except Exception as exc:
            print(f"! recalcul des prix de référence en erreur: {exc}")

    if DISCOVERY_ENABLED:
        try:
            newly = discover_new_products(products)
            if SEARCH_DISCOVERY_ENABLED:
                newly += discover_via_search_engines(products)
            if newly:
                activate_new_discoveries(state, products, newly)
            else:
                products[:] = load_products()
            state["last_discovery"] = time.time()
            save_state(state)
        except Exception as exc:
            print(f"! découverte automatique en erreur: {exc}")

    if args.once:
        for product in products:
            state["products"].setdefault(product["url"], new_entry())["next_check"] = 0
        safe_cycle(state, products)
        return

    if args.fast:
        end = time.monotonic() + max(30, args.duration)
        while time.monotonic() < end:
            for product in products:
                entry = state["products"].setdefault(product["url"], new_entry())
                entry["next_check"] = 0
            safe_cycle(state, products)
            if DISCOVERY_ENABLED and time.time() - state.get("last_discovery", 0) >= min(DISCOVERY_EVERY, 300):
                try:
                    newly = discover_new_products(products)
                    if SEARCH_DISCOVERY_ENABLED:
                        newly += discover_via_search_engines(products)
                    if newly:
                        activate_new_discoveries(state, products, newly)
                    else:
                        products[:] = load_products()
                    state["last_discovery"] = time.time()
                    save_state(state)
                except Exception as exc:
                    print(f"! découverte automatique en erreur: {exc}")
            time.sleep(max(MIN_INTERVAL, args.interval) + random.uniform(0, 3))
        print("Mode rapide terminé.")
        return

    print(
        "Bot lancé — prix de référence + "
        f"{PRICE_TOLERANCE_PCT:g}% | {len(products)} produits."
    )
    print("Ctrl+C pour arrêter.")

    try:
        while True:
            safe_cycle(state, products)
            if DISCOVERY_ENABLED and time.time() - state.get("last_discovery", 0) >= DISCOVERY_EVERY:
                try:
                    newly = discover_new_products(products)
                    if SEARCH_DISCOVERY_ENABLED:
                        newly += discover_via_search_engines(products)
                    if newly:
                        activate_new_discoveries(state, products, newly)
                    else:
                        products[:] = load_products()
                    state["last_discovery"] = time.time()
                    save_state(state)
                except Exception as exc:
                    print(f"! découverte automatique en erreur: {exc}")
            time.sleep(3)
    except KeyboardInterrupt:
        print("\nArrêt.")

if __name__ == "__main__":
    main()
