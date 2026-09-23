#!/usr/bin/env python3
"""
Bot de surveillance Pokémon / One Piece TCG — V25 (Toutes sorties TCG + Syntaxes 30 ans & Lyon).
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
# CONFIGURATION GENERALE
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
PHYSICAL_ALERT_COOLDOWN = int(os.environ.get("PHYSICAL_ALERT_COOLDOWN", "600"))
PHYSICAL_STORE_RADIUS_LABEL = os.environ.get("PHYSICAL_STORE_RADIUS_LABEL", "Lyon métropole")

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
ALERT_COOLDOWN_HOURS = int(os.environ.get("ALERT_COOLDOWN_HOURS", "6"))

BASE_DIR = Path(__file__).resolve().parent
PRODUCTS_FILE = BASE_DIR / "products.txt"
STATE_FILE = BASE_DIR / "stock_state.json"
DISCOVERY_FILE = BASE_DIR / "discovered_products.txt"

AUTO_ADD_DISCOVERED = os.environ.get("AUTO_ADD_DISCOVERED", "1") != "0"
DISCOVERY_ENABLED = os.environ.get("DISCOVERY_ENABLED", "1") != "0"
DISCOVERY_EVERY = int(os.environ.get("DISCOVERY_EVERY", "180"))

# MOTS CLES ET TERMES DE PURGE / DECOUVERTE
PURGE_PRODUCT_TERMS = (
    "storm emerald", "storm emerald m6", "eb-05", "eb05", "heroines edition vol. 2",
)

DISCOVERY_KEYWORDS = (
    "pokemon", "pokémon", "one-piece", "onepiece", "one_piece", "optcg",
    "op-", "eb-", "me-", "ev-", "sv-", "display", "booster", "etb", "coffret",
    "bundle", "blister", "pack", "box", "30th", "30ans", "30-ans", "delta",
)

# Produits prioritaires : passe immédiatement en surveillance accélérée à la découverte
DROP_PRIORITY_TERMS = (
    # One Piece
    "op17", "op-17", "op 17", "double pack", "double-pack", "duo pack", "duo-pack",
    "op18", "op-18", "op 18", "the dominance of god", "dominance of god",
    # Pokémon 30 ans (Toutes les syntaxes)
    "30e anniversaire", "30ème anniversaire", "30eme anniversaire",
    "30 ème anniversaire", "30 eme anniversaire", "30th anniversary", "30th-anniversary",
    "30th celebration", "30 ans", "30ans", "30 ans pokémon", "pokémon 30 ans",
    # Règne Delta
    "règne delta", "règne delta m6", "delta reign", "me06",
    # Coffrets majeurs
    "upc", "ultra premium",
)
DROP_PRIORITY_INTERVAL = int(os.environ.get("DROP_PRIORITY_INTERVAL", "10"))

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/128.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "fr-FR,fr;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept-Encoding": "gzip, deflate, br" if HAS_BROTLI else "gzip, deflate",
    "Sec-Ch-Ua": '"Chromium";v="128", "Not=A?Brand";v="24", "Google Chrome";v="128"',
    "Sec-Ch-Ua-Mobile": "?0",
    "Sec-Ch-Ua-Platform": '"Windows"',
    "Upgrade-Insecure-Requests": "1",
}

TRANSIENT_HTTP = {408, 425, 429, 500, 502, 503, 504}

# ---------------------------------------------------------------------------
# FILTRES PRODUITS (TOUTES SORTIES + CIBLES SPÉCIFIQUES)
# ---------------------------------------------------------------------------

IN_KEYS = {"instock", "limitedavailability", "onlineonly", "instoreonly", "availablefororder", "true"}
PRE_KEYS = {"preorder", "presale", "backorder"}
OUT_KEYS = {"outofstock", "soldout", "discontinued", "oos", "false"}

SCHEMA_RE = re.compile(
    r'(?:schema\.org/|"availability"\s*:\s*")'
    r"(InStock|LimitedAvailability|OnlineOnly|InStoreOnly|PreOrder|PreSale|BackOrder|OutOfStock|SoldOut|Discontinued)",
    re.I,
)
OG_RES = [
    re.compile(r"""(?:product|og):availability["']\s+content=["']([^"']+)["']""", re.I),
    re.compile(r"""content=["']([^"']+)["']\s+(?:property|name)=["'](?:product|og):availability["']""", re.I),
]
LD_RE = re.compile(r"""<script[^>]+type=["']application/ld\+json["'][^>]*>(.*?)</script>""", re.I | re.S)
NEXT_DATA_RE = re.compile(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', re.I | re.S)

OUT_WORDS = ["épuisé", "epuise", "rupture de stock", "out of stock", "sold out", "indisponible", "plus disponible", "victime de son succès"]
IN_WORDS = ["ajouter au panier", "add to cart", "ajouter à la commande", "acheter maintenant", "commander"]
PRE_WORDS = ["précommande", "precommande", "pre-order", "preorder"]
BLOCK_WORDS = ["captcha", "access denied", "just a moment", "datadome", "verify you are human", "unusual traffic", "robot check", "cf-chl"]


def is_relevant_pokemon_candidate(title: str, url: str = "") -> bool:
    """Valide TOUT produit Pokémon TCG (standard ou spécial)."""
    haystack = f"{title} {url}".lower()
    pokemon = any(x in haystack for x in ("pokemon", "pokémon", "pokemon tcg", "pokémon tcg", "pokemon jcc", "pokémon jcc"))
    product_term = (
        any(x in haystack for x in (
            "etb", "coffret", "bundle", "booster", "display", "booster box",
            "box", "pack", "tripack", "duopack", "collection", "tin", "mini tin",
            "blister", "deck", "starter deck", "upc", "ultra premium",
            "règne delta", "delta reign", "30 ans", "30th"
        ))
        or re.search(r"\bme\d{2}\b", haystack) is not None
        or re.search(r"\bev\d{2}\b", haystack) is not None
        or re.search(r"\beb\d{2}\b", haystack) is not None
        or re.search(r"\bsv\d{2}\b", haystack) is not None
        or re.search(r"\bupc\b", haystack) is not None
    )
    return pokemon and product_term


def is_relevant_onepiece_candidate(title: str, url: str = "") -> bool:
    """Valide TOUT produit One Piece TCG (OP01 à OP99, EB01, etc.)."""
    haystack = f"{title} {url}".lower()
    one_piece = any(x in haystack for x in ("one piece", "onepiece", "one-piece", "optcg"))
    product_term = (
        re.search(r"\bop\s*-?\s*\d{1,2}\b", haystack) is not None
        or re.search(r"\beb\s*-?\s*\d{1,2}\b", haystack) is not None
        or any(x in haystack for x in (
            "dominance of god", "duo pack", "duo-pack", "double pack", "double-pack",
            "booster", "display", "booster box", "starter deck", "deck", "box", "collection"
        ))
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
    return any(isinstance(x, str) and x.lower() in ("product", "productgroup", "individualproduct") for x in types)

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

PRICE_RE = re.compile(r"""(?<![\d.,])(\d{1,4}(?:[ .]\d{3})*(?:[,.]\d{1,2})?)\s*(?:€|EUR)\b""", re.I)
PRICE_RE_REV = re.compile(r"""(?:€|EUR)\s*(\d{1,4}(?:[ .]\d{3})*(?:[,.]\d{1,2})?)(?![\d.,])""", re.I)

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
        val = float(s)
    except ValueError:
        return None
    if not (0 < val < 100000):
        return None
    return round(val, 2)

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
    proxy = os.environ.get("HTTPS_PROXY") or os.environ.get("HTTP_PROXY")
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({"http": proxy, "https": proxy})) if proxy else urllib.request.build_opener()

    try:
        with opener.open(req, timeout=REQUEST_TIMEOUT) as response:
            raw = response.read(MAX_PAGE_BYTES)
            encoding = (response.headers.get("Content-Encoding") or "").lower()
            charset = response.headers.get_content_charset() or "utf-8"
    except urllib.error.HTTPError as exc:
        raise FetchError(_http_message(exc.code), exc.code in TRANSIENT_HTTP, exc.code) from exc

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
        except (urllib.error.URLError, http.client.HTTPException, OSError, zlib.error, EOFError) as exc:
            last = FetchError(f"réseau ({exc.__class__.__name__})", True)

        if not last.transient or attempt >= FETCH_RETRIES:
            raise last
        time.sleep(1.5 * (attempt + 1) + random.random())
    if last:
        raise last
    raise FetchError("Erreur réseau indéterminée")

# ---------------------------------------------------------------------------
# NOTIFICATIONS
# ---------------------------------------------------------------------------

def _header(text: str, limit: int = 200) -> str:
    return " ".join(str(text).split()).encode("latin-1", "replace").decode("latin-1")[:limit]

def notify(title: str, message: str, url: str = "", priority: str = "5", tags: str = "rotating_light") -> bool:
    if TOPIC_UNSET:
        print("  ! NTFY_TOPIC non configuré.")
        return False

    endpoint = "https://ntfy.sh/" + urllib.parse.quote(NTFY_TOPIC, safe="")
    headers = {"Title": _header(title), "Priority": str(priority), "Tags": tags}
    if url:
        headers["Click"] = url

    data = str(message)[:1800].encode("utf-8")

    for attempt in range(3):
        try:
            req = urllib.request.Request(endpoint, data=data, headers=headers, method="POST")
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
# PRODUCTS & STATE
# ---------------------------------------------------------------------------

LINE_RE = re.compile(r"^(.+?)\s*\|\s*(https?://\S+)\s*\|\s*([0-9]+(?:[.,][0-9]{1,2})?)\s*$")

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
            print(f"! ligne {line_no} ignorée: format attendu 'Nom | URL | prix_normal'")
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
        products.append({"name": name, "url": url, "reference_price": reference_price})

    if not products:
        raise RuntimeError("products.txt ne contient aucun produit valide.")
    return products

def new_entry():
    return {
        "status": None, "alerted": False, "weak_hits": 0, "problem_since": 0,
        "problem_alerted": False, "next_check": 0, "cooldown_until": 0,
        "last_http_status": None, "errors": 0, "last_price": None,
        "physical_status": None, "physical_stores": [], "physical_checked_at": 0,
        "physical_last_alert": 0,
    }

def new_state():
    return {"products": {}, "last_crash_alert": 0}

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

    if isinstance(data.get("last_crash_alert"), (int, float)):
        state["last_crash_alert"] = data["last_crash_alert"]

    if isinstance(data.get("products"), dict):
        for url, old in data["products"].items():
            entry = new_entry()
            if isinstance(old, dict):
                entry.update({k: old[k] for k in entry if k in old})
            state["products"][str(url)] = entry

    return state

def save_state(state):
    try:
        payload = json.dumps(state, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        tmp = STATE_FILE.with_name(STATE_FILE.name + ".tmp")
        tmp.write_text(payload, encoding="utf-8")
        os.replace(tmp, STATE_FILE)
    except Exception as exc:
        print(f"! écriture state impossible: {exc}")

# ---------------------------------------------------------------------------
# PHYSICAL STOCK (MAGASIN LYON)
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
        "disponible pour retrait", "disponible au retrait", "available to collect",
    )
    explicit_out = (
        "indisponible en magasin", "non disponible en magasin",
        "aucun magasin disponible", "pas disponible en magasin",
    )
    has_out = any(x in low for x in explicit_out)
    positive_phrases = tuple(x for x in explicit_in if x not in ("disponible en magasin", "disponible dans votre magasin"))
    has_in = any(x in low for x in positive_phrases)

    aliases = {
        "Fnac Lyon Bellecour": ("fnac lyon bellecour", "fnac bellecour", "fnac lyon 2"),
        "Fnac Lyon Part-Dieu": ("fnac lyon part-dieu", "fnac part-dieu", "fnac lyon part dieu"),
        "Fnac Lyon - Gare Part-Dieu": ("fnac lyon - gare part-dieu", "fnac gare part-dieu"),
        "Carrefour Lyon Part Dieu": ("carrefour lyon part dieu", "carrefour part dieu"),
        "Carrefour Lyon Confluence": ("carrefour lyon confluence", "carrefour confluence"),
        "Carrefour Market Lyon Frères Lumière": ("carrefour market lyon freres lumiere",),
        "Carrefour Vénissieux": ("carrefour venissieux",),
        "Auchan Supermarché Lyon Gerland": ("auchan supermarche lyon gerland", "auchan lyon gerland"),
        "Auchan Supermarché Lyon Félix Faure": ("auchan supermarche lyon felix faure",),
        "Auchan Supermarché Garibaldi - Lyon": ("auchan garibaldi",),
        "King Jouet Lyon Grolée": ("king jouet lyon grolee",),
        "King Jouet Boutique Lyon 4ème": ("king jouet lyon 4eme",),
        "Smyths Toys Bron": ("smyths toys bron",),
        "JouéClub Lyon Confluence": ("joueclub lyon confluence", "joueclub lyon"),
        "La Grande Récré LYON La Part Dieu": ("la grande recre la part dieu",),
        "Micromania - Zing LYON CENTRE VILLE": ("micromania lyon centre ville",),
        "Micromania - Zing LYON PART DIEU": ("micromania lyon part dieu",),
        "Micromania - Zing LYON GRENETTE": ("micromania lyon grenette",),
    }

    stores = []
    try:
        blobs = []
        m = NEXT_DATA_RE.search(html)
        if m: blobs.append(json.loads(m.group(1)))
        for data in _ld_nodes(html): blobs.append(data)

        for data in blobs:
            for node in _walk(data):
                if not isinstance(node, dict): continue
                flat = norm_text(" ".join(str(v) for v in node.values() if isinstance(v, (str, int, float, bool))))
                for store, variants in aliases.items():
                    if any(v in flat for v in variants):
                        if any(marker in flat for marker in explicit_in):
                            stores.append(store)
    except Exception:
        pass

    for store, variants in aliases.items():
        for variant in variants:
            pos = low.find(variant)
            if pos >= 0:
                context = low[max(0, pos - 1800):min(len(low), pos + 2600)]
                if any(x in context for x in explicit_in) and not any(x in context for x in explicit_out):
                    stores.append(store)
                    break

    stores = list(dict.fromkeys(stores))
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

def maybe_notify_physical(state: dict, result: dict):
    if not PHYSICAL_ALERT_ENABLED or result.get("physical_status") != "in":
        return
    entry = state["products"].setdefault(result["url"], new_entry())
    current = tuple(result.get("physical_stores") or [])
    previous = tuple(entry.get("physical_stores") or [])
    now = time.time()
    changed = (not previous) or current != previous or entry.get("physical_status") != "in"
    cooldown_ok = now - float(entry.get("physical_last_alert", 0) or 0) >= PHYSICAL_ALERT_COOLDOWN

    if current and changed and cooldown_ok:
        where = "\n".join(f"🟢 {store} : STOCK DÉTECTÉ" for store in current)
        notify(
            f"🏬 Stock magasin Lyon : {result['name']}",
            f"🏬 STOCK MAGASIN DÉTECTÉ — {result['name']}\nZone : {PHYSICAL_STORE_RADIUS_LABEL}\n{where}\n{result['url']}",
            priority="5",
            tags="shopping_cart",
        )
        entry["physical_last_alert"] = now
    entry["physical_status"] = result.get("physical_status")
    entry["physical_stores"] = list(current)
    entry["physical_checked_at"] = result.get("physical_checked_at", now)

# ---------------------------------------------------------------------------
# DECOUVERTE DE NOUVEAUX PRODUITS (SITEMAP XML)
# ---------------------------------------------------------------------------

def _extract_sitemap_urls(base_url: str) -> list[str]:
    host = f"{urlparse(base_url).scheme}://{urlparse(base_url).netloc}"
    robots_url = host.rstrip("/") + "/robots.txt"
    urls = []
    try:
        text = fetch(robots_url)
        for line in text.splitlines():
            if line.lower().startswith("sitemap:"):
                u = line.split(":", 1)[1].strip()
                if u.startswith("http"): urls.append(u)
    except Exception:
        pass
    if not urls:
        urls = [host.rstrip("/") + "/sitemap.xml"]
    return list(dict.fromkeys(urls))[:5]

def _parse_sitemap(xml: str) -> list[str]:
    return re.findall(r"<loc>\s*(https?://[^<\s]+)\s*</loc>", xml, re.I)

def discover_new_products(products: list[dict]) -> list[dict]:
    if not DISCOVERY_ENABLED:
        return []

    discovered = []
    known_hosts = set(urlparse(p["url"]).netloc.lower() for p in products)
    known_urls = set(p["url"].rstrip("/") for p in products)

    for host in known_hosts:
        base_url = f"https://{host}"
        sitemap_urls = _extract_sitemap_urls(base_url)
        for sitemap in sitemap_urls:
            try:
                xml = fetch(sitemap)
                urls = _parse_sitemap(xml)
                for u in urls:
                    clean_u = u.rstrip("/")
                    if clean_u in known_urls:
                        continue
                    low_u = u.lower()
                    if any(k in low_u for k in DISCOVERY_KEYWORDS):
                        try:
                            html = fetch(u)
                            title = _product_title(html, u)
                            if is_relevant_pokemon_candidate(title, u) or is_relevant_onepiece_candidate(title, u):
                                price = extract_price(html)
                                if price:
                                    item = {"name": title, "url": clean_u, "reference_price": price}
                                    discovered.append(item)
                                    known_urls.add(clean_u)
                        except Exception:
                            continue
            except Exception:
                continue

    if discovered and AUTO_ADD_DISCOVERED:
        additions = [f"{item['name']} | {item['url']} | {item['reference_price']:.2f}" for item in discovered]
        current = PRODUCTS_FILE.read_text(encoding="utf-8-sig") if PRODUCTS_FILE.exists() else ""
        PRODUCTS_FILE.write_text(current.rstrip() + "\n" + "\n".join(additions) + "\n", encoding="utf-8")
        print(f"+ {len(additions)} produit(s) découvert(s) via Sitemap et ajouté(s) à products.txt")

    return discovered

def _product_title(html: str, fallback_url: str) -> str:
    for pat in (
        r'<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)',
        r'<title[^>]*>\s*([^<]+?)\s*</title>',
    ):
        m = re.search(pat, html, re.I | re.S)
        if m:
            title = re.sub(r"\s+", " ", m.group(1)).strip()
            if title: return title[:180]
    return urlparse(fallback_url).path.rstrip("/").split("/")[-1].replace("-", " ")[:180]

# ---------------------------------------------------------------------------
# CYCLE RUNNER
# ---------------------------------------------------------------------------

def check_one(product: dict) -> dict:
    result = {**product, "status": None, "source": None, "price": None, "error": None, "http_status": None, "physical_status": None, "physical_stores": [], "physical_checked_at": 0}
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
        result["error"] = f"erreur inattendue ({exc.__class__.__name__}: {str(exc)[:80]})"
    return result

def due(product, entry, now):
    return now >= float(entry.get("next_check", 0))

def schedule_next(entry, result, now):
    status = result.get("status")
    http_status = result.get("http_status")
    errors = int(entry.get("errors", 0))

    if http_status in (429, 403):
        cooldown = COOLDOWN_429 if http_status == 429 else COOLDOWN_403
        entry["cooldown_until"] = now + cooldown
        entry["next_check"] = now + cooldown
        return

    if result.get("error"):
        errors += 1
        entry["errors"] = min(errors, 8)
        interval = min(MAX_INTERVAL, DEFAULT_INTERVAL * (2 ** min(errors, 4)))
    else:
        entry["errors"] = 0
        entry["cooldown_until"] = 0
        drop_hay = f"{entry.get('name', '')} {entry.get('url', '')}".lower()
        if any(term in drop_hay for term in DROP_PRIORITY_TERMS):
            interval = DROP_PRIORITY_INTERVAL
        elif status in ("in", "preorder") or entry.get("alerted"):
            interval = PRIORITY_INTERVAL
        else:
            interval = DEFAULT_INTERVAL

    jitter = random.uniform(-0.10, 0.10) * interval
    entry["next_check"] = now + max(MIN_INTERVAL, int(interval + jitter))

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

    entry["problem_since"] = 0
    entry["status"] = result["status"]
    entry["last_price"] = result["price"]

    maybe_notify_physical(state, result)

    price_ok = True
    if PRICE_FILTER_ENABLED:
        if result["price"] is None:
            price_ok = not PRICE_REQUIRED
        else:
            ceiling = accepted_price(result["reference_price"])
            price_ok = result["price"] <= ceiling

    available = result["status"] == "in" or (result["status"] == "preorder" and ALERT_ON_PREORDER)

    if available and price_ok and not entry["alerted"]:
        title = f"Stock dispo : {result['name']}" if result["status"] == "in" else f"Précommande : {result['name']}"
        msg = f"{result['name']}\nPrix : {result['price']} €\n{result['url']}"
        if notify(title, msg, result["url"]):
            entry["alerted"] = True

    schedule_next(entry, result, now)

def run_due(state, products, deadline):
    now = time.time()
    due_products = [p for p in products if due(p, state["products"].setdefault(p["url"], new_entry()), now)]

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

    with ThreadPoolExecutor(max_workers=max(1, min(MAX_WORKERS, len(groups)))) as pool:
        futures = [pool.submit(worker, g) for g in groups.values()]
        for future in as_completed(futures):
            results.extend(future.result())

    checked, available, errors = 0, 0, 0
    for r in results:
        checked += 1
        if r.get("error"): errors += 1
        elif r.get("status") in ("in", "preorder"): available += 1
        process_result(state, r)

    return checked, available, errors

def purge_obsolete_products() -> int:
    try:
        current = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        return 0

    kept, removed = [], 0
    for raw in current.splitlines():
        line = raw.strip()
        m = LINE_RE.match(line) if line and not line.startswith("#") else None
        if not m:
            kept.append(raw)
            continue

        name, url = m.group(1).strip(), m.group(2).strip()
        if any(term in f"{name} {url}".lower() for term in PURGE_PRODUCT_TERMS):
            removed += 1
            continue
        kept.append(raw)

    if removed:
        PRODUCTS_FILE.write_text("\n".join(kept).rstrip() + "\n", encoding="utf-8")
    return removed

# ---------------------------------------------------------------------------
# MAIN CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Bot de surveillance Pokémon/One Piece TCG.")
    parser.add_argument("--once", action="store_true", help="vérification unique")
    parser.add_argument("--test", action="store_true", help="test ntfy")
    args = parser.parse_args()

    if args.test:
        sys.exit(0 if notify("Test bot", "Notifications fonctionnelles.") else 1)

    purge_obsolete_products()
    products = load_products()
    state = load_state()

    if DISCOVERY_ENABLED:
        try:
            discover_new_products(products)
            products = load_products()
        except Exception as exc:
            print(f"! Erreur lors de la découverte : {exc}")

    print(f"Bot lancé avec {len(products)} produits surveillés.")
    try:
        last_discovery = time.time()
        while True:
            run_due(state, products, time.monotonic() + RUN_DEADLINE)
            save_state(state)

            if DISCOVERY_ENABLED and (time.time() - last_discovery) >= DISCOVERY_EVERY:
                discover_new_products(products)
                products = load_products()
                last_discovery = time.time()

            if args.once:
                break
            time.sleep(3)
    except KeyboardInterrupt:
        print("\nArrêt du bot.")

if __name__ == "__main__":
    main()
