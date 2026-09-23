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
import html as html_lib
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
DISCOVERY_FILE = BASE_DIR / "discovered_products.txt"
AUTO_ADD_DISCOVERED = os.environ.get("AUTO_ADD_DISCOVERED", "1") != "0"
DISCOVERY_ENABLED = os.environ.get("DISCOVERY_ENABLED", "1") != "0"
DISCOVERY_MAX_PER_HOST = int(os.environ.get("DISCOVERY_MAX_PER_HOST", "12"))
DISCOVERY_TIMEOUT = int(os.environ.get("DISCOVERY_TIMEOUT", "12"))
DISCOVERY_EVERY = int(os.environ.get("DISCOVERY_EVERY", "300"))
SEARCH_DISCOVERY_ENABLED = os.environ.get("SEARCH_DISCOVERY_ENABLED", "1") != "0"
SEARCH_ENGINE = os.environ.get("SEARCH_ENGINE", "both").lower()
SEARCH_RESULTS_PER_QUERY = int(os.environ.get("SEARCH_RESULTS_PER_QUERY", "6"))
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
# AUTO-DISCOVERY DES NOUVEAUX PRODUITS
# ---------------------------------------------------------------------------

DISCOVERY_KEYWORDS = (
    "pokemon", "pokémon", "one-piece", "onepiece", "one_piece",
    "op-", "op17", "op18", "eb-", "eb05", "display", "booster",
    "etb", "coffret", "bundle", "blister", "pack", "box",
)

# Sorties futures à surveiller explicitement. Cela évite de dépendre uniquement
# de requêtes génériques lorsque le nom commercial vient juste d'apparaître.
DISCOVERY_WATCH_TERMS = (
    "OP-18", "OP18", "The Dominance of God",
    "EB-05", "Heroines Edition Vol. 2",
    "30e Anniversaire", "30th Celebration", "30 ans",
    "Storm Emerald", "Storm Emerald M6",
)


def _extract_sitemap_urls(base_url: str) -> list[str]:
    """Trouve les sitemaps déclarés par robots.txt, puis extrait leurs URLs."""
    host = f"{urlparse(base_url).scheme}://{urlparse(base_url).netloc}"
    robots_url = host.rstrip("/") + "/robots.txt"
    urls = []
    try:
        text = fetch(robots_url)
        for line in text.splitlines():
            if line.lower().startswith("sitemap:"):
                u = line.split(":", 1)[1].strip()
                if u.startswith("http"):
                    urls.append(u)
    except Exception:
        pass
    if not urls:
        urls = [host.rstrip("/") + "/sitemap.xml"]
    return list(dict.fromkeys(urls))[:5]


def _parse_sitemap(xml: str) -> list[str]:
    # Suffisant pour sitemap.xml et sitemap-index sans dépendance XML externe.
    return re.findall(r"<loc>\s*(https?://[^<\s]+)\s*</loc>", xml, re.I)


def _discovery_candidate(url: str) -> bool:
    low = urllib.parse.unquote(url).lower()
    return any(k in low for k in DISCOVERY_KEYWORDS)


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


def _load_discovered_urls() -> set[str]:
    seen = set()
    if DISCOVERY_FILE.exists():
        try:
            for line in DISCOVERY_FILE.read_text(encoding="utf-8").splitlines():
                if "|" in line and not line.lstrip().startswith("#"):
                    parts = [x.strip() for x in line.split("|")]
                    if len(parts) >= 2:
                        seen.add(parts[1])
        except OSError:
            pass
    return seen



# ---------------------------------------------------------------------------
# PRIX DE RÉFÉRENCE : ENSEIGNE UNIQUEMENT
# ---------------------------------------------------------------------------

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
    """Retourne uniquement les prix d'offres dont le vendeur est l'enseigne.

    Si une page ne fournit aucun vendeur structuré, on considère son prix comme
    direct-enseigne (cas fréquent des fiches sans marketplace). Dès qu'une offre
    structurée comporte un vendeur, seules les offres explicitement attribuées à
    l'enseigne sont retenues.
    """
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
        # La page expose des vendeurs mais aucun n'est l'enseigne : marketplace
        # uniquement, donc surtout ne pas utiliser son prix comme référence.
        return []
    fallback = extract_price(html)
    return [fallback] if fallback is not None and fallback > 0 else []


def _reference_price_from_retailer(html: str, retailer: str):
    prices = _official_retailer_prices(html, retailer)
    if not prices:
        return None
    # S'il y a plusieurs offres directes de l'enseigne, le prix le plus bas est
    # le seuil réellement affiché par cette enseigne, sans prendre un vendeur tiers.
    return min(prices)




def _extract_gtin_candidates(html: str) -> list[str]:
    """Extrait des EAN/GTIN-13 visibles dans les données structurées de la fiche."""
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
    """Construit des recherches assez strictes pour retrouver le même produit."""
    qs = []
    for ean in _extract_gtin_candidates(html):
        qs.append(ean)
    title = _product_title(html, "")
    if title:
        # Nettoyage des mentions de boutique pour ne pas biaiser la recherche.
        clean = re.sub(r"^(?:[^|]+\s-\s)+", "", title).strip()
        qs.append('"' + clean[:120] + '"')
    if name:
        clean_name = re.sub(r"^[^|]+\s-\s", "", name).strip()
        if clean_name:
            qs.append('"' + clean_name[:120] + '"')
    return list(dict.fromkeys(qs))

def _find_official_price_for_product(name: str, source_url: str, source_html: str):
    """Cherche le prix enseigne officiel du même produit dans les grandes enseignes."""
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
                # Une correspondance EAN est idéale. À défaut, exige plusieurs
                # éléments du nom pour éviter de confondre deux coffrets proches.
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
    """Recalcule les prix de référence à partir des grandes enseignes uniquement."""
    if not AUTO_REFRESH_PRICES:
        return 0
    changed = 0
    rows = []
    try:
        text = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        return 0
    product_by_url = {p["url"].rstrip("/"): p for p in products}
    for raw in text.splitlines():
        line = raw.strip()
        m = LINE_RE.match(line) if line and not line.startswith("#") else None
        if not m:
            rows.append(raw)
            continue
        name, url, old_price = m.group(1).strip(), m.group(2).strip(), parse_price(m.group(3))
        if old_price is None:
            rows.append(raw); continue
        # Ne cherche le prix de référence que pour Pokémon / One Piece.
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
    """Ajoute les nouvelles fiches validées directement dans products.txt."""
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

# ---------------------------------------------------------------------------
# RECHERCHE GOOGLE / BING + GRANDES ENSEIGNES
# ---------------------------------------------------------------------------

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
    # Google utilise plusieurs variantes de liens selon la page retournée.
    for m in re.finditer(r'href=["\'](/url\?q=|)(https?://[^"\'&<>]+)', text, re.I):
        u = html_lib.unescape(m.group(2))
        if u not in found:
            found.append(u)
    # Variante /url?q=...&sa=...
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
    """Découvre et active automatiquement les nouveautés chez les grandes enseignes.

    Aucune notification de découverte n'est envoyée. Une fiche n'est ajoutée à
    products.txt que si son prix peut être rattaché à l'enseigne elle-même, et non
    à un vendeur marketplace. Le prix ainsi obtenu devient la référence du produit;
    le filtre habituel +10 % décide ensuite si une alerte de disponibilité part.
    """
    if not SEARCH_DISCOVERY_ENABLED or not AUTO_ADD_DISCOVERED:
        return []

    known = {p["url"].rstrip("/") for p in products}
    discovered = []

    for domain, (retailer, families) in DISCOVERY_RETAILERS.items():
        queries = [
            f'site:{domain} (pokemon OR pokémon) ("30e Anniversaire" OR "30th Celebration" OR "30 ans" OR "Storm Emerald" OR "Storm Emerald M6")',
            f'site:{domain} ("One Piece" OR OP-18 OR OP18 OR EB-05 OR EB05 OR "Heroines Edition") (précommande OR acheter OR stock OR display OR booster)',
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
                low = (title + " " + url).lower()
                if not ("pokemon" in low or "pokémon" in low or "one piece" in low or "one-piece" in low):
                    continue
                if not any(x in low for x in ("booster", "display", "coffret", "etb", "pack", "box", "deck")):
                    continue

                reference_price = _reference_price_from_retailer(html, retailer)
                if reference_price is None:
                    # Pas de prix fiable vendu par l'enseigne elle-même : on ignore
                    # la fiche pour éviter d'apprendre un prix marketplace/spéculatif.
                    continue
                status, source = classify(html)
                item = {
                    "name": f"{retailer} - {title}",
                    "url": clean,
                    "reference_price": reference_price,
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
        # Les produits seront repris dans la liste active au tour suivant.
        print(f"+ {added} nouveau(x) produit(s) ajouté(s) automatiquement à products.txt")
    return discovered

def discover_new_products(products: list[dict]) -> list[dict]:
    """Compatibilité historique : la découverte active passe par Google/Bing.

    Les sitemaps de boutiques spécialisées ne servent plus à définir un prix de
    référence. Cela évite qu'un prix élevé d'un revendeur soit appris comme prix
    normal. Les grandes enseignes sont traitées par discover_via_search_engines().
    """
    return []

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
# CLI
# ---------------------------------------------------------------------------

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
    args = parser.parse_args()

    if args.test:
        sys.exit(0 if notify(
            "Test bot Pokémon",
            "Les notifications ntfy fonctionnent.",
            priority="3",
            tags="white_check_mark",
        ) else 1)

    try:
        products = load_products()
    except RuntimeError as exc:
        print(f"! {exc}")
        sys.exit(2)

    state = load_state()

    # Recalcule périodiquement les prix de référence à partir des grandes
    # enseignes uniquement. Aucun prix Marketplace/spécialiste n'est utilisé.
    last_price_refresh = state.get("last_price_refresh", 0)
    if AUTO_REFRESH_PRICES and (time.time() - last_price_refresh >= PRICE_REFRESH_HOURS * 3600 or args.once):
        try:
            refresh_existing_reference_prices(products)
            products[:] = load_products()
            state["last_price_refresh"] = time.time()
            save_state(state)
        except Exception as exc:
            print(f"! recalcul des prix de référence en erreur: {exc}")

    # Découverte automatique au démarrage. Les nouvelles fiches validées par une
    # grande enseigne sont ajoutées directement à products.txt, sans notification
    # de découverte. Les notifications restent réservées aux disponibilités au
    # prix de référence autorisé.
    if DISCOVERY_ENABLED:
        try:
            discover_new_products(products)
            if SEARCH_DISCOVERY_ENABLED:
                discover_via_search_engines(products)
                products[:] = load_products()
            # Les fiches découvertes avec précommande/stock sont immédiatement
            # reprises par le scheduler au tour suivant, sans notification de
            # "découverte" : seule la notification de disponibilité est envoyée.
            state["last_discovery"] = time.time()
            save_state(state)
        except Exception as exc:
            print(f"! découverte automatique en erreur: {exc}")

    if args.once:
        # --once ignore le scheduler pour vérifier tout le fichier.
        for product in products:
            state["products"].setdefault(product["url"], new_entry())["next_check"] = 0
        safe_cycle(state, products)
        return

    if args.fast:
        end = time.monotonic() + max(30, args.duration)
        while time.monotonic() < end:
            # En mode rapide, on force les produits à être dus à chaque tour.
            for product in products:
                entry = state["products"].setdefault(product["url"], new_entry())
                entry["next_check"] = 0
            safe_cycle(state, products)
            if DISCOVERY_ENABLED and time.time() - state.get("last_discovery", 0) >= min(DISCOVERY_EVERY, 300):
                try:
                    discover_new_products(products)
                    if SEARCH_DISCOVERY_ENABLED:
                        discover_via_search_engines(products)
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
                    discover_new_products(products)
                    if SEARCH_DISCOVERY_ENABLED:
                        discover_via_search_engines(products)
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
