#!/usr/bin/env python3
"""
Bot de surveillance Pokémon / One Piece TCG — V15
- Surveillance stock/prix
- Découverte multi-enseignes via Google/Bing
- Détection renforcée des portfolios/classeurs/binders
- Journal réel des découvertes dans discovered_products.txt
- Auto-ajout dans products.txt
- Scan stock magasin Lyon
- Gestion ntfy, prix, cooldowns et état persistant

V15 : recherche française TCG stricte, file de découvertes persistante et catalogues directs ; corrige notamment les cas où une fiche comme
"Smyths Toys - Pokémon - Portfolio avec Boosters - Modèle Aléatoire"
est trouvée mais rejetée parce que "portfolio" n'était pas reconnu.
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

NTFY_TOPIC = (os.environ.get("NTFY_TOPIC") or "").strip()
TOPIC_UNSET = not NTFY_TOPIC

PRICE_FILTER_ENABLED = os.environ.get("PRICE_FILTER_ENABLED", "1") != "0"
PRICE_REQUIRED = os.environ.get("PRICE_REQUIRED", "1") != "0"
PRICE_TOLERANCE_PCT = float(os.environ.get("PRICE_TOLERANCE_PCT", "10"))
ALERT_ON_PREORDER = os.environ.get("ALERT_ON_PREORDER", "1") != "0"

PHYSICAL_STOCK_ENABLED = os.environ.get("PHYSICAL_STOCK_ENABLED", "1") != "0"
PHYSICAL_ALERT_ENABLED = os.environ.get("PHYSICAL_ALERT_ENABLED", "1") != "0"
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
).split("|") if x.strip())

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

# V16 : découverte directe des catalogues/pages TCG des enseignes.
CATALOG_DISCOVERY_ENABLED = os.environ.get("CATALOG_DISCOVERY_ENABLED", "1") != "0"
CATALOG_DISCOVERY_EVERY = int(os.environ.get("CATALOG_DISCOVERY_EVERY", "1800"))
CATALOG_MAX_PAGES_PER_HOST = int(os.environ.get("CATALOG_MAX_PAGES_PER_HOST", "2"))
CATALOG_MAX_PRODUCTS_PER_HOST = int(os.environ.get("CATALOG_MAX_PRODUCTS_PER_HOST", "12"))
CATALOG_FETCH_WORKERS = int(os.environ.get("CATALOG_FETCH_WORKERS", "6"))

SEARCH_DISCOVERY_ENABLED = os.environ.get("SEARCH_DISCOVERY_ENABLED", "1") != "0"
SEARCH_ENGINE = os.environ.get("SEARCH_ENGINE", "both").lower()
SEARCH_RESULTS_PER_QUERY = int(os.environ.get("SEARCH_RESULTS_PER_QUERY", "8"))
SEARCH_QUERIES_PER_HOST = int(os.environ.get("SEARCH_QUERIES_PER_HOST", "6"))
SEARCH_TIMEOUT = int(os.environ.get("SEARCH_TIMEOUT", "12"))

AUTO_REFRESH_PRICES = os.environ.get("AUTO_REFRESH_PRICES", "1") != "0"
PRICE_REFRESH_HOURS = float(os.environ.get("PRICE_REFRESH_HOURS", "12"))

DISCOVERY_IMMEDIATE_CHECK = os.environ.get("DISCOVERY_IMMEDIATE_CHECK", "1") != "0"
DISCOVERY_LOG_ALL_CANDIDATES = os.environ.get("DISCOVERY_LOG_ALL_CANDIDATES", "0") == "1"

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
# NORMALISATION / UTILITAIRES
# ---------------------------------------------------------------------------

def normalize_text(value) -> str:
    value = html_lib.unescape(str(value or "")).lower()
    value = unicodedata.normalize("NFKD", value)
    value = "".join(c for c in value if not unicodedata.combining(c))
    value = value.replace("’", "'")
    return re.sub(r"\s+", " ", value).strip()

def compact(value) -> str:
    return re.sub(r"[^a-z0-9]", "", normalize_text(value))

def _norm(value) -> str:
    return compact(str(value).rsplit("/", 1)[-1])

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

# ---------------------------------------------------------------------------
# STOCK
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
    re.compile(r"""(?:product|og):availability["']\s+content=["']([^"']+)["']""", re.I),
    re.compile(r"""content=["']([^"']+)["']\s+(?:property|name)=["'](?:product|og):availability["']""", re.I),
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

    low = normalize_text(html)
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
# CANDIDATS PRODUITS
# ---------------------------------------------------------------------------

POKEMON_PRODUCT_TERMS = (
    # Signaux TCG forts
    "etb", "elite trainer box", "coffret", "booster", "display",
    "booster box", "boite de boosters", "bundle", "pack 2 boosters",
    "pack 3 boosters", "tripack", "tri-pack", "duopack", "duo pack",
    "duo-pack", "double pack", "blister", "deck", "starter deck",
    "deck de combat", "deckbox", "deck box", "pokebox", "poke box",
    "pokébox", "mini tin", "tin", "premium collection",
    "ultra premium collection", "upc", "collection premium",
    # Rangement explicitement lié aux cartes / boosters
    "portfolio", "portefeuille", "classeur", "binder", "album",
    "album de collection", "collectors album", "collector album",
    "range-cartes", "range cartes", "cahier range-cartes",
)

# Produits Pokémon qui ne sont PAS du TCG. Ces termes sont volontairement
# stricts afin qu'une catégorie générale Pokémon (351+ articles chez certaines
# enseignes) ne transforme pas LEGO, peluches, figurines, etc. en candidats TCG.
POKEMON_TCG_BLOCK_TERMS = (
    "lego", "peluche", "peluche", "figurine", "funko", "tonies", "tonie",
    "lampe", "veilleuse", "montre", "reveil", "réveil", "puzzle",
    "toupie", "spinner", "megablocks", "mega bloks", "mega bloks",
    "jeu de société", "jeu de societe", "cherche et trouve", "livre",
    "roman", "manga", "sticker", "autocollant", "vetement", "vêtement",
    "chaussette", "sac à dos", "sac a dos", "gourde", "mug", "lampe",
    "ceinture de dresseur", "clip n' go", "clip n go", "accessoire",
    "jouet à construire", "jouet a construire", "set de construction",
)

# Termes qui prouvent beaucoup mieux qu'une fiche est bien du JCC Pokémon.
POKEMON_TCG_STRONG_TERMS = (
    "pokemon tcg", "pokémon tcg", "pokemon jcc", "pokémon jcc",
    "jeu de cartes à collectionner", "jeu de cartes a collectionner",
    "trading card game", "trading cards", "booster", "boosters",
    "carte promo", "cartes promo", "cartes à collectionner",
    "cartes a collectionner", "display", "etb", "elite trainer box",
    "deck de combat", "league battle deck", "world championships", "championnats du monde", "académie de combat", "academie de combat", "deck", "pokébox", "pokebox", "mini tin",
    "portfolio", "classeur", "binder", "range-cartes", "range cartes",
)

# One Piece : références FR recherchées. Les noms de sets anglais ne sont
# volontairement PAS utilisés dans les requêtes de découverte.
ONEPIECE_PRODUCT_TERMS = (
    "ts-03", "ts03", "ts 03", "tin pack", "boîte métal", "boite metal",
    "boîte métallique", "boite metallique",
    "op-17", "op17", "op 17", "op-18", "op18", "op 18",
    "op-19", "op19", "op 19",
    "duo pack", "duo-pack", "double pack", "double-pack",
    "booster", "display", "booster box", "box", "pack", "deck",
    "starter deck", "double pack",
)

# Un produit explicitement identifié comme anglais est rejeté. On ne demande
# pas la présence obligatoire du mot "français" : de nombreuses fiches FR
# n'indiquent pas la langue, surtout chez les grandes enseignes françaises.
ENGLISH_TCG_MARKERS = (
    "anglais", "anglaise", "english", "en anglais",
    "version anglaise", "version anglaise", "english version",
    "english edition", "uk version", "us version",
)

def _is_explicitly_english_tcg(title: str = "", url: str = "", html: str = "") -> bool:
    # Ne regarde pas tout le HTML : une enseigne peut avoir un bouton
    # de langue "English" dans son footer sans que le produit soit anglais.
    title_url = normalize_text(f"{title} {url}")
    if any(normalize_text(x) in title_url for x in ENGLISH_TCG_MARKERS):
        return True
    visible = _visible_product_text(html, 20000) if html else ""
    # On exige un contexte produit autour du marqueur anglais.
    for marker in ENGLISH_TCG_MARKERS:
        m = normalize_text(marker)
        if m not in visible:
            continue
        for context_word in (
            "version", "edition", "édition", "langue", "language",
            "carte", "cartes", "cards", "booster", "display", "pack", "deck",
        ):
            if re.search(rf"{re.escape(context_word)}.{{0,45}}{re.escape(m)}|{re.escape(m)}.{{0,45}}{re.escape(context_word)}", visible):
                return True
    return False

ONEPIECE_TCG_BLOCK_TERMS = (
    "figurine", "peluche", "funko", "lego", "mug", "vetement",
    "vêtement", "lampe", "puzzle", "poster", "livre", "manga",
    "jeu de société", "jeu de societe", "jouet", "statue",
)

DISCOVERY_WATCH_TERMS = (
    "30e anniversaire", "30eme anniversaire", "30ème anniversaire",
    "30 ans", "30ans", "30 ans pokemon", "pokemon 30 ans",
    "portfolio", "classeur", "binder", "album",
    "one piece card game", "one piece tcg",
    "ts-03", "ts03", "ts 03", "tin pack",
    "op-17", "op17", "op 17", "op-18", "op18", "op 18",
    "op-19", "op19", "op 19",
    "règne delta", "regne delta", "me06",
)

DROP_PRIORITY_TERMS = (
    "op17", "op-17", "op 17", "op18", "op-18", "op 18",
    "op19", "op-19", "op 19",
    "ts03", "ts-03", "ts 03", "tin pack",
    "30e anniversaire", "30ème anniversaire", "30eme anniversaire",
    "30 ans", "30ans", "30 ans pokemon", "pokemon 30 ans",
    "portfolio", "classeur", "binder", "album",
    "règne delta", "regne delta", "me06",
)
DROP_PRIORITY_INTERVAL = int(os.environ.get("DROP_PRIORITY_INTERVAL", "10"))

def _visible_product_text(html: str, limit: int = 60000) -> str:
    if not html:
        return ""
    visible = re.sub(r"<script\b[^>]*>.*?</script>", " ", html, flags=re.I | re.S)
    visible = re.sub(r"<style\b[^>]*>.*?</style>", " ", visible, flags=re.I | re.S)
    visible = re.sub(r"<noscript\b[^>]*>.*?</noscript>", " ", visible, flags=re.I | re.S)
    visible = re.sub(r"<[^>]+>", " ", visible)
    return normalize_text(visible[:limit])

def _has_any(text: str, terms) -> bool:
    return any(normalize_text(term) in text for term in terms)

def is_relevant_pokemon_candidate(title: str, url: str = "", html: str = "") -> bool:
    if _is_explicitly_english_tcg(title, url, html):
        return False
    title_url = normalize_text(f"{title} {url}")
    visible = _visible_product_text(html)
    pokemon = _has_any(title_url, (
        "pokemon", "pokémon", "pokemon tcg", "pokémon tcg",
        "pokemon jcc", "pokémon jcc",
    )) or _has_any(visible[:30000], (
        "pokemon tcg", "pokémon tcg", "pokemon jcc", "pokémon jcc"
    ))
    if not pokemon:
        return False

    title_blocked = _has_any(title_url, POKEMON_TCG_BLOCK_TERMS)
    title_has_tcg = _has_any(title_url, POKEMON_PRODUCT_TERMS)
    content_has_tcg = _has_any(visible[:50000], POKEMON_TCG_STRONG_TERMS)

    if title_blocked and not title_has_tcg:
        return False

    generic_storage = _has_any(title_url, (
        "portfolio", "classeur", "binder", "album", "range-cartes", "range cartes"
    ))
    if generic_storage:
        return pokemon and (
            content_has_tcg or _has_any(title_url, (
                "booster", "boosters", "cartes", "cards",
                "pokemon tcg", "pokemon jcc"
            ))
        )

    if title_has_tcg and not title_blocked:
        return True
    return content_has_tcg and not title_blocked

def is_relevant_onepiece_candidate(title: str, url: str = "", html: str = "") -> bool:
    if _is_explicitly_english_tcg(title, url, html):
        return False
    title_url = normalize_text(f"{title} {url}")
    visible = _visible_product_text(html)
    one_piece = (
        _has_any(title_url, ("one piece", "onepiece", "one-piece"))
        or _has_any(visible[:30000], ("one piece card game", "one piece tcg"))
    )
    if not one_piece:
        return False
    blocked = _has_any(title_url, ONEPIECE_TCG_BLOCK_TERMS)
    strong = (
        _has_any(title_url, ONEPIECE_PRODUCT_TERMS)
        or _has_any(visible[:50000], (
            "one piece card game", "one piece tcg", "booster", "display",
            "starter deck", "deck", "ts-03", "ts03", "tin pack"
        ))
    )
    return bool(strong and not blocked)

# ---------------------------------------------------------------------------
# PRIX
# ---------------------------------------------------------------------------

PRICE_RE = re.compile(
    r"""(?<![\d.,])(\d{1,4}(?:[ .]\d{3})*(?:[,.]\d{1,2})?)\s*(?:€|EUR)\b""", re.I
)
PRICE_RE_REV = re.compile(
    r"""(?:€|EUR)\s*(\d{1,4}(?:[ .]\d{3})*(?:[,.]\d{1,2})?)(?![\d.,])""", re.I
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
    return round(value, 2) if 0 < value < 100000 else None

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
            if isinstance(node.get("offers"), (dict, list)):
                for offer in _walk(node["offers"]):
                    if isinstance(offer, dict):
                        for key in ("price", "lowPrice"):
                            p = parse_price(offer.get(key))
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
        if isinstance(node, dict):
            for key in ("price", "salePrice", "currentPrice", "sellingPrice"):
                p = parse_price(node.get(key))
                if p is not None:
                    prices.append(p)
    return prices

def extract_price(html: str):
    prices = _collect_json_prices(html) + _collect_next_prices(html)
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
    return sorted(set(round(p, 2) for p in prices))[0]

# ---------------------------------------------------------------------------
# RÉSEAU
# ---------------------------------------------------------------------------

class FetchError(Exception):
    def __init__(self, message, transient=False, status_code=None):
        super().__init__(message)
        self.transient = transient
        self.status_code = status_code

def _http_message(code: int) -> str:
    return {
        403: "HTTP 403 (accès refusé / protection anti-bot probable)",
        404: "HTTP 404 (page introuvable)",
        429: "HTTP 429 (trop de requêtes)",
    }.get(code, f"HTTP {code}")

def _fetch_once(url: str, timeout=None) -> str:
    req = urllib.request.Request(url, headers=HEADERS)
    proxy = os.environ.get("HTTPS_PROXY") or os.environ.get("HTTP_PROXY") or \
            os.environ.get("https_proxy") or os.environ.get("http_proxy")
    opener = urllib.request.build_opener(
        urllib.request.ProxyHandler({"http": proxy, "https": proxy})
    ) if proxy else urllib.request.build_opener()

    try:
        with opener.open(req, timeout=timeout or REQUEST_TIMEOUT) as response:
            raw = response.read(MAX_PAGE_BYTES)
            encoding = (response.headers.get("Content-Encoding") or "").lower()
            charset = response.headers.get_content_charset() or "utf-8"
    except urllib.error.HTTPError as exc:
        raise FetchError(_http_message(exc.code), exc.code in TRANSIENT_HTTP, exc.code)
    except urllib.error.URLError as exc:
        raise FetchError(f"réseau ({exc})", True)

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
        except (http.client.HTTPException, OSError, zlib.error, EOFError) as exc:
            last = FetchError(f"réseau ({exc.__class__.__name__})", True)
        if not last.transient or attempt >= FETCH_RETRIES:
            raise last
        time.sleep(1.5 * (attempt + 1) + random.random())
    raise last

# ---------------------------------------------------------------------------
# NOTIFICATIONS
# ---------------------------------------------------------------------------

def _header(text: str, limit: int = 200) -> str:
    return " ".join(str(text).split()).encode("latin-1", "replace").decode("latin-1")[:limit]

def notify(title: str, message: str, url: str = "", priority: str = "5",
           tags: str = "rotating_light") -> bool:
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
# PRODUCTS / STATE
# ---------------------------------------------------------------------------

LINE_RE = re.compile(r"^(.+?)\s*\|\s*(https?://\S+)\s*\|\s*([0-9]+(?:[.,][0-9]{1,2})?)\s*$")

def load_products():
    try:
        text = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except FileNotFoundError:
        raise RuntimeError("products.txt est introuvable à côté du script.")
    products, seen = [], set()
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
        name, url = match.group(1).strip(), match.group(2).strip()
        price = parse_price(match.group(3))
        if price is None:
            continue
        key = url.rstrip("/")
        if key in seen:
            continue
        seen.add(key)
        products.append({"name": name, "url": url, "reference_price": price})
    if not products:
        raise RuntimeError("products.txt ne contient aucun produit valide.")
    return products

def new_entry():
    return {
        "status": None, "alerted": False, "weak_hits": 0,
        "problem_since": 0, "problem_alerted": False,
        "next_check": 0, "cooldown_until": 0,
        "last_http_status": None, "errors": 0, "last_price": None,
        "physical_status": None, "physical_stores": [],
        "physical_checked_at": 0, "physical_last_alert": 0,
        "name": "", "url": "",
    }

def new_state():
    return {"products": {}, "last_heartbeat": 0, "last_crash_alert": 0,
            "last_config_alert": 0, "last_price_refresh": 0, "last_discovery": 0,
            "last_catalog_discovery": 0}

def load_state():
    state = new_state()
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return state
    except FileNotFoundError:
        return state
    except Exception as exc:
        print(f"! état illisible ({exc}); nouveau state.")
        return state

    for key in state:
        if key != "products" and isinstance(data.get(key), (int, float)):
            state[key] = data[key]
    if isinstance(data.get("products"), dict):
        for url, old in data["products"].items():
            entry = new_entry()
            if isinstance(old, dict):
                for k in entry:
                    if k in old:
                        entry[k] = old[k]
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
# STOCK MAGASIN LYON
# ---------------------------------------------------------------------------

def _physical_status_from_html(html: str, retailer: str = ""):
    if not html:
        return None, []

    low = normalize_text(html)
    explicit_in = (
        "en stock en magasin", "stock en magasin", "disponible en magasin",
        "disponible dans votre magasin", "disponible dans ce magasin",
        "disponible dans le magasin", "en rayon", "retrait 1h en magasin",
        "retrait 1h gratuit", "retrait sous 2h", "disponible pour retrait",
        "disponible au retrait", "available to collect",
    )
    explicit_out = (
        "indisponible en magasin", "non disponible en magasin",
        "aucun magasin disponible", "pas disponible en magasin",
    )
    aliases = {
        "Fnac Lyon Bellecour": ("fnac lyon bellecour", "fnac bellecour", "fnac lyon 2"),
        "Fnac Lyon Part-Dieu": ("fnac lyon part-dieu", "fnac part-dieu", "fnac lyon part dieu"),
        "Fnac Lyon - Gare Part-Dieu": ("fnac gare part-dieu",),
        "Carrefour Lyon Part Dieu": ("carrefour lyon part dieu", "carrefour part dieu"),
        "Carrefour Lyon Confluence": ("carrefour lyon confluence", "carrefour confluence"),
        "Carrefour Market Lyon Frères Lumière": ("carrefour market lyon freres lumiere", "carrefour freres lumiere"),
        "Carrefour Vénissieux": ("carrefour venissieux",),
        "Auchan Supermarché Lyon Gerland": ("auchan lyon gerland",),
        "Auchan Supermarché Lyon Félix Faure": ("auchan lyon felix faure",),
        "Auchan Supermarché Garibaldi - Lyon": ("auchan garibaldi",),
        "Auchan Supermarché City Lyon Université": ("auchan lyon universite",),
        "King Jouet Lyon Grolée": ("king jouet lyon grolee", "king jouet lyon grolée"),
        "King Jouet Boutique Lyon 4ème": ("king jouet boutique lyon 4eme",),
        "King Jouet Orchestra Lyon/Carré de Soie": ("king jouet carre de soie",),
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
    for store, variants in aliases.items():
        for variant in variants:
            pos = low.find(variant)
            if pos < 0:
                continue
            context = low[max(0, pos - 1800):min(len(low), pos + 2600)]
            if any(x in context for x in explicit_in) and not any(x in context for x in explicit_out):
                stores.append(store)
                break

    if stores:
        return "in", list(dict.fromkeys(stores))
    has_out = any(x in low for x in explicit_out)
    has_in = any(x in low for x in explicit_in)
    if has_out and not has_in:
        return "out", []
    if has_in:
        return "possible", []
    return None, []

def physical_result(product, html):
    status, stores = _physical_status_from_html(html, urlparse(product["url"]).netloc)
    return {"physical_status": status, "physical_stores": stores,
            "physical_checked_at": time.time()}

def maybe_notify_physical(state, result):
    if not PHYSICAL_ALERT_ENABLED or result.get("physical_status") != "in":
        return
    entry = state["products"].setdefault(result["url"], new_entry())
    current = tuple(result.get("physical_stores") or [])
    previous = tuple(entry.get("physical_stores") or [])
    changed = (not previous) or current != previous or entry.get("physical_status") != "in"
    cooldown_ok = time.time() - float(entry.get("physical_last_alert", 0) or 0) >= PHYSICAL_ALERT_COOLDOWN
    if current and changed and cooldown_ok:
        stores = "\n".join(f"🟢 {x} : STOCK DÉTECTÉ" for x in current)
        price = result.get("price")
        price_txt = f"Prix en ligne : {price:.2f} €" if isinstance(price, (int, float)) else "Prix en ligne : non déterminé"
        notify(
            f"🏬 Stock magasin Lyon : {result['name']}",
            f"🏬 STOCK MAGASIN DÉTECTÉ — {result['name']}\n"
            f"Zone : {PHYSICAL_STORE_RADIUS_LABEL}\n{stores}\n{price_txt}\n{result['url']}",
            priority="5", tags="shopping_cart,department_store"
        )
        entry["physical_last_alert"] = time.time()
    entry["physical_status"] = result.get("physical_status")
    entry["physical_stores"] = list(current)
    entry["physical_checked_at"] = result.get("physical_checked_at", time.time())

# ---------------------------------------------------------------------------
# CHECK PRODUIT
# ---------------------------------------------------------------------------

def accepted_price(reference_price):
    return round(reference_price * (1 + PRICE_TOLERANCE_PCT / 100.0), 2)

def check_one(product):
    result = {**product, "status": None, "source": None, "price": None,
              "error": None, "http_status": None, "physical_status": None,
              "physical_stores": [], "physical_checked_at": 0}
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
    return not entry.get("next_check") or now >= float(entry.get("next_check", 0))

def schedule_next(entry, result, now):
    status, http_status = result.get("status"), result.get("http_status")
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
        hay = normalize_text(f"{entry.get('name', '')} {entry.get('url', '')}")
        interval = DROP_PRIORITY_INTERVAL if any(x in hay for x in DROP_PRIORITY_TERMS) else (
            PRIORITY_INTERVAL if status in ("in", "preorder") or entry.get("alerted")
            else DEFAULT_INTERVAL
        )
    interval = max(MIN_INTERVAL, int(interval + random.uniform(-.10, .10) * interval))
    entry["next_check"] = now + interval

def process_result(state, result):
    url = result["url"]
    entry = state["products"].setdefault(url, new_entry())
    entry["name"], entry["url"] = result.get("name", ""), url
    now = time.time()

    if result["error"]:
        if not entry["problem_since"]:
            entry["problem_since"] = now
        print(f"- {result['name']}: ERREUR {result['error']}")
        schedule_next(entry, result, now)
        return

    if entry["problem_alerted"]:
        notify("Bot Pokémon : site de nouveau lisible", result["name"], result["url"],
               priority="2", tags="white_check_mark")
    entry["problem_since"] = 0
    entry["problem_alerted"] = False
    entry["last_http_status"] = 200
    entry["status"] = result["status"]
    entry["last_price"] = result["price"]

    maybe_notify_physical(state, result)

    labels = {"in": "EN STOCK", "preorder": "PRÉCOMMANDE", "out": "épuisé",
              "blocked": "BLOQUÉ", "unknown": "INCONNU"}
    price_txt = f" | prix {result['price']:.2f} €" if result["price"] is not None else ""
    print(f"- {result['name']}: {labels.get(result['status'], result['status'])} [{result['source']}]{price_txt}")

    is_in_stock = result["status"] == "in"
    is_preorder = result["status"] == "preorder" and ALERT_ON_PREORDER
    if not (is_in_stock or is_preorder):
        entry["alerted"], entry["weak_hits"] = False, 0
        schedule_next(entry, result, now)
        return

    if PRICE_FILTER_ENABLED:
        if result["price"] is None:
            if PRICE_REQUIRED:
                entry["alerted"], entry["weak_hits"] = False, 0
                schedule_next(entry, result, now)
                return
        elif result["price"] > accepted_price(result["reference_price"]):
            print(f"  -> prix refusé: {result['price']:.2f} € > plafond {accepted_price(result['reference_price']):.2f} €")
            entry["alerted"], entry["weak_hits"] = False, 0
            schedule_next(entry, result, now)
            return

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
            if PRICE_FILTER_ENABLED else "Filtre prix désactivé."
        )
        title = f"Stock dispo : {result['name']}" if is_in_stock else f"Précommande : {result['name']}"
        if notify(title, f"{result['name']}\n\n{price_text}\n\n{result['url']}\n\nSource stock : {result['source']}",
                  result["url"], priority="5", tags="rotating_light"):
            entry["alerted"] = True
    schedule_next(entry, result, now)

def run_due(state, products, deadline):
    now = time.time()
    due_products = [p for p in products if due(p, state["products"].setdefault(p["url"], new_entry()), now)]
    if not due_products:
        return 0, 0, 0

    groups = {}
    for product in due_products:
        groups.setdefault(urlparse(product["url"]).netloc.lower(), []).append(product)

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

    checked = available = errors = 0
    for result in results:
        checked += 1
        errors += bool(result.get("error"))
        available += result.get("status") in ("in", "preorder")
        process_result(state, result)
    return checked, available, errors

def safe_cycle(state, products):
    try:
        started = time.monotonic()
        checked, available, errors = run_due(state, products, started + RUN_DEADLINE)
        save_state(state)
        if checked:
            print(f"[{datetime.now():%H:%M:%S}] {checked} vérif(s), {available} dispo(s), {errors} erreur(s), {time.monotonic()-started:.1f}s")
    except Exception:
        trace = traceback.format_exc()
        print(trace)
        if time.time() - state.get("last_crash_alert", 0) >= ALERT_COOLDOWN_HOURS * 3600:
            notify("Bot Pokémon : erreur interne", trace[-1200:], priority="4", tags="warning")
            state["last_crash_alert"] = time.time()
        save_state(state)

# ---------------------------------------------------------------------------
# PURGE
# ---------------------------------------------------------------------------

PURGE_PRODUCT_TERMS = ("storm emerald", "storm emerald m6", "eb-05", "eb05", "heroines edition vol. 2")

def purge_obsolete_products():
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
        hay = normalize_text(f"{m.group(1)} {m.group(2)}")
        if any(term in hay for term in PURGE_PRODUCT_TERMS):
            removed += 1
            print(f"- ancienne cible supprimée de products.txt : {m.group(1)}")
        else:
            kept.append(raw)
    if removed:
        PRODUCTS_FILE.write_text("\n".join(kept).rstrip() + "\n", encoding="utf-8")
    return removed

# ---------------------------------------------------------------------------
# DISCOVERY
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

# Pages catalogue officielles connues. Elles complètent Google/Bing.
CATALOG_SEEDS = {
    "fnac.com": ["https://www.fnac.com/n529205/Jeux-de-recre-cartes-a-collectionner/Cartes-Pokemon"],
    "carrefour.fr": ["https://www.carrefour.fr/s?q=pokemon%20cartes"],
    "auchan.fr": ["https://www.auchan.fr/pokemon/ep-pokemon"],
    "cultura.com": [
        "https://www.cultura.com/index/index-des-licences/univers-pokemon/cartes-pokemon.html",
        "https://www.cultura.com/cartes-a-jouer/cartes-pokemon.html?p=1",
    ],
    "king-jouet.com": [
        "https://www.king-jouet.com/jeux-jouets-pokemon.htm",
        "https://www.king-jouet.com/jeux-jouets/tout-le-site-hors-livres-piles/pokemon/page1.htm",
    ],
    "smythstoys.com": [
        "https://www.smythstoys.com/fr/fr-fr/jouets/jeux-de-societe-et-puzzles/cartes-a-collectionner/cartes-pokemon/c/SM1301061101",
        "https://www.smythstoys.com/fr/fr-fr/jouets/jeux-de-societe-et-puzzles/cartes-a-collectionner/cartes-pokemon/nouveautes-cartes-pokemon/c/nouveautes-cartes-pokemon",
    ],
    "joueclub.fr": ["https://www.joueclub.fr/contenu/les-cartes-pokemon.html"],
    "lagranderecre.fr": ["https://www.lagranderecre.fr/jouet-pokemon.html"],
}
CATALOG_DOMAIN_RETAILERS = {domain: DISCOVERY_RETAILERS[domain][0] for domain in CATALOG_SEEDS}

def _absolute_url(base_url: str, href: str):
    href = html_lib.unescape((href or "").strip())
    if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
        return None
    return _clean_candidate_url(urllib.parse.urljoin(base_url, href))


def _catalog_links(html: str, base_url: str, domain: str):
    found, seen = [], set()
    host = domain.lower().lstrip("www.")
    rx = re.compile(r'<a\b[^>]+href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', re.I | re.S)
    for m in rx.finditer(html):
        url = _absolute_url(base_url, m.group(1))
        if not url:
            continue
        parsed = urlparse(url)
        if parsed.netloc.lower().split(":")[0].lstrip("www.") != host:
            continue
        key = url.rstrip("/")
        if key in seen:
            continue
        path = normalize_text(parsed.path)
        if any(x in path for x in ("/search", "/recherche", "/account", "/login", "/panier", "/cart", "/wishlist")):
            continue
        anchor = normalize_text(re.sub(r"<[^>]+>", " ", m.group(2)))
        hay = f"{anchor} {path}"
        score = 0
        if any(x in hay for x in ("pokemon", "pokémon", "one piece", "onepiece")):
            score += 6
        for term in POKEMON_PRODUCT_TERMS + ONEPIECE_PRODUCT_TERMS:
            if normalize_text(term) in hay:
                score += 2
        if any(x in hay for x in ("30e anniversaire", "30eme anniversaire", "30ème anniversaire", "30 ans", "portfolio", "classeur", "booster")):
            score += 3
        if score < 6:
            continue
        seen.add(key)
        found.append((score, anchor[:180], url))
    found.sort(key=lambda x: (-x[0], x[2]))
    return found


def _catalog_page_links(html: str, base_url: str, domain: str):
    links, seen = [], set()
    host = domain.lower().lstrip("www.")
    rx = re.compile(r'<a\b[^>]+href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', re.I | re.S)
    for m in rx.finditer(html):
        url = _absolute_url(base_url, m.group(1))
        if not url:
            continue
        p = urlparse(url)
        if p.netloc.lower().split(":")[0].lstrip("www.") != host:
            continue
        label = normalize_text(re.sub(r"<[^>]+>", " ", m.group(2)))
        hay = f"{label} {p.path} {p.query}".lower()
        if not any(x in hay for x in ("page=", "page/", "p=", "start=", "offset=", "suivant", "next")):
            continue
        key = url.rstrip("/")
        if key not in seen:
            seen.add(key)
            links.append(url)
    return links


def _catalog_candidate_from_page(retailer, url, html):
    title = _product_title(html, url)
    if not (
        is_relevant_pokemon_candidate(title, url, html)
        or is_relevant_onepiece_candidate(title, url, html)
    ):
        return None
    status, source = classify(html)
    score, reasons = _score_candidate(retailer, title, url, html)
    if score < 6:
        return None
    price = _reference_price_from_retailer(html, retailer)
    return {
        "name": f"{retailer} - {title}", "url": url,
        "reference_price": price, "reference_source": retailer,
        "price": price, "status": status, "source": source,
        "discovery_score": score, "discovery_reasons": reasons + ["catalogue-direct"],
    }

def discover_via_catalogs(products):
    if not CATALOG_DISCOVERY_ENABLED:
        return []
    known = {p["url"].rstrip("/") for p in products}
    discovered, global_seen = [], set(known)
    for domain, seeds in CATALOG_SEEDS.items():
        retailer = CATALOG_DOMAIN_RETAILERS[domain]
        print(f"  📚 Catalogue direct: {retailer}")
        pages = []
        seen_pages = set()
        for seed in seeds:
            if len(pages) >= CATALOG_MAX_PAGES_PER_HOST:
                break
            try:
                html = _fetch_once(seed, DISCOVERY_TIMEOUT)
                pages.append((seed, html)); seen_pages.add(seed.rstrip("/"))
            except Exception as exc:
                if DISCOVERY_LOG_ALL_CANDIDATES:
                    print(f"    ! catalogue inaccessible {seed}: {exc}")
        # Une page suivante éventuelle, sans crawler toute la pagination.
        if len(pages) < CATALOG_MAX_PAGES_PER_HOST:
            for seed, html in list(pages):
                for nxt in _catalog_page_links(html, seed, domain):
                    if len(pages) >= CATALOG_MAX_PAGES_PER_HOST:
                        break
                    key = nxt.rstrip("/")
                    if key in seen_pages:
                        continue
                    try:
                        nxt_html = _fetch_once(nxt, DISCOVERY_TIMEOUT)
                        pages.append((nxt, nxt_html)); seen_pages.add(key)
                    except Exception:
                        continue
        candidates = {}
        for page_url, html in pages:
            for score, anchor, url in _catalog_links(html, page_url, domain):
                key = url.rstrip("/")
                if key not in global_seen and key not in candidates:
                    candidates[key] = (score, anchor, url)
        selected = sorted(candidates.values(), key=lambda x: (-x[0], x[2]))[:CATALOG_MAX_PRODUCTS_PER_HOST]
        if not selected:
            print("    ℹ️ aucun lien TCG candidat exploitable.")
            continue
        def worker(item):
            try:
                html = _fetch_once(item[2], DISCOVERY_TIMEOUT)
                return _catalog_candidate_from_page(retailer, item[2], html)
            except Exception as exc:
                if DISCOVERY_LOG_ALL_CANDIDATES:
                    print(f"    ! fiche inaccessible {item[2]}: {exc}")
                return None
        with ThreadPoolExecutor(max_workers=max(1, CATALOG_FETCH_WORKERS)) as pool:
            futures = [pool.submit(worker, item) for item in selected]
            for future in as_completed(futures):
                item = future.result()
                if not item:
                    continue
                key = item["url"].rstrip("/")
                if key in global_seen:
                    continue
                global_seen.add(key); discovered.append(item)
                print(f"    ✅ CATALOGUE [{retailer}] {item['name'].split(' - ', 1)[-1][:100]} | {item['reference_price']:.2f} €")
    return discovered


def _product_title(html: str, fallback_url: str) -> str:
    patterns = (
        r'<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)',
        r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:title',
        r'<title[^>]*>\s*([^<]+?)\s*</title>',
        r'"name"\s*:\s*"([^"\\]{3,180})"',
    )
    for pat in patterns:
        m = re.search(pat, html, re.I | re.S)
        if m:
            title = re.sub(r"\s+", " ", html_lib.unescape(m.group(1))).strip()
            if title:
                return title[:180]
    path = urllib.parse.unquote(urlparse(fallback_url).path.rstrip("/").split("/")[-1])
    return path.replace("-", " ").replace("_", " ")[:180]

def _seller_matches_retailer(seller, retailer):
    if not seller:
        return False
    low, wanted = compact(seller), compact(retailer)
    aliases = {
        "fnac": {"fnac", "fnaccom"}, "carrefour": {"carrefour", "carrefourfr"},
        "auchan": {"auchan", "auchanfr"}, "cultura": {"cultura", "culturacom"},
        "kingjouet": {"kingjouet", "kingjouetcom"}, "smythstoys": {"smythstoys", "smythstoyscom"},
        "joueclub": {"joueclub", "joueclubfr"}, "lagranderecre": {"lagranderecre", "lagranderecrefr"},
        "micromania": {"micromania", "micromaniafr"},
    }
    return low == wanted or low in aliases.get(wanted, {wanted})

def _official_retailer_prices(html, retailer):
    prices, structured_offers = [], False
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
                        p = parse_price(offer.get("price"))
                        if p is not None:
                            prices.append(p)
                else:
                    p = parse_price(offer.get("price"))
                    if p is not None:
                        prices.append(p)
    if prices:
        return prices
    if structured_offers:
        return []
    p = extract_price(html)
    return [p] if p is not None else []

def _reference_price_from_retailer(html, retailer):
    prices = _official_retailer_prices(html, retailer)
    return min(prices) if prices else None

def _valid_ean13(value: str) -> bool:
    value = re.sub(r"\D", "", str(value or ""))
    if len(value) != 13:
        return False
    total = sum(int(value[i]) * (1 if i % 2 == 0 else 3) for i in range(12))
    check = (10 - (total % 10)) % 10
    return check == int(value[-1])

def _extract_gtin_candidates(html):
    vals = []
    # Priorité aux champs structurés explicites.
    explicit = (
        r'"gtin13"\s*:\s*"?(\d{13})',
        r'"gtin"\s*:\s*"?(\d{13})',
        r'"ean13"\s*:\s*"?(\d{13})',
        r'"ean"\s*:\s*"?(\d{13})',
        r'(?i)(?:EAN|GTIN)[^0-9]{0,30}(\d{13})',
    )
    for pat in explicit:
        for m in re.finditer(pat, html):
            value = m.group(1)
            if _valid_ean13(value) and value not in vals:
                vals.append(value)
            if len(vals) >= 5:
                return vals
    return vals

def _candidate_product_queries(name, html):
    qs = _extract_gtin_candidates(html)
    title = _product_title(html, "")
    if title:
        qs.append('"' + title[:120] + '"')
    if name:
        qs.append('"' + re.sub(r"^[^|]+\s-\s", "", name).strip()[:120] + '"')
    return list(dict.fromkeys(qs))

def _search_result_urls_google(query):
    url = "https://www.google.com/search?" + urllib.parse.urlencode(
        {"q": query, "num": SEARCH_RESULTS_PER_QUERY, "hl": "fr", "gl": "fr"}
    )
    try:
        text = _fetch_once(url, SEARCH_TIMEOUT)
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

def _search_result_urls_bing(query):
    url = "https://www.bing.com/search?" + urllib.parse.urlencode(
        {"q": query, "count": SEARCH_RESULTS_PER_QUERY, "setlang": "fr-FR"}
    )
    try:
        text = _fetch_once(url, SEARCH_TIMEOUT)
    except Exception:
        return []
    found = []
    for m in re.finditer(
        r'<li[^>]*class=["\'][^"\']*b_algo[^"\']*["\'][\s\S]*?<h2[^>]*>\s*<a[^>]+href=["\']([^"\']+)',
        text, re.I
    ):
        u = html_lib.unescape(m.group(1))
        if u.startswith("http") and u not in found:
            found.append(u)
    return found[:SEARCH_RESULTS_PER_QUERY * 2]

def _search_engine_urls(query):
    urls = []
    if SEARCH_ENGINE in ("google", "both"):
        urls.extend(_search_result_urls_google(query))
    if SEARCH_ENGINE in ("bing", "both"):
        urls.extend(_search_result_urls_bing(query))
    return list(dict.fromkeys(urls))

def _clean_candidate_url(url):
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https") or not parsed.netloc:
        return None
    clean = parsed._replace(fragment="").geturl().rstrip("/")
    path = parsed.path.lower()
    if any(x in path for x in ("/search", "/recherche", "/account", "/login", "/panier", "/cart")):
        return None
    return clean

def _discovery_queries(domain):
    # Recherche volontairement orientée FR. Aucun nom de set anglais n'est
    # injecté dans les requêtes TCG. Les pages explicitement anglaises sont
    # ensuite rejetées par _is_explicitly_english_tcg().
    return [
        f'site:{domain} (pokemon OR pokémon) ("30 ans" OR "30e anniversaire" OR "30ème anniversaire") (portfolio OR classeur OR binder OR album OR booster OR coffret OR ETB) (précommande OR acheter OR stock OR disponible) -anglais -english',
        f'site:{domain} (pokemon OR pokémon) ("Règne Delta" OR ME06) (coffret OR ETB OR booster OR display OR pack OR blister OR deck) (précommande OR acheter OR stock OR disponible) -anglais -english',
        f'site:{domain} (pokemon OR pokémon) (portfolio OR classeur OR binder OR album) (booster OR cartes OR "jeu de cartes") -anglais -english',
        f'site:{domain} (pokemon OR pokémon) (ETB OR coffret OR booster OR display OR pack OR bundle OR collection OR tin OR blister OR deck) (précommande OR acheter OR stock OR disponible) -anglais -english',
        f'site:{domain} ("One Piece Card Game" OR "One Piece TCG") ("TS-03" OR TS03 OR "Tin Pack" OR "boîte métal" OR "boite metal") (précommande OR acheter OR stock OR disponible OR français OR francaise) -anglais -english',
        f'site:{domain} ("One Piece Card Game" OR "One Piece TCG") ("OP-17" OR OP17 OR "OP 17" OR "OP-18" OR OP18 OR "OP 18") (booster OR display OR pack OR coffret) (précommande OR acheter OR stock OR disponible) -anglais -english',
    ]

def _score_candidate(retailer, title, url, html):
    hay = normalize_text(f"{title} {url}")
    visible = normalize_text(re.sub(r"<[^>]+>", " ", html[:250000]))
    alltext = f"{hay} {visible}"
    score = 0
    reasons = []

    if "pokemon" in alltext or "pokémon" in alltext:
        score += 5
        reasons.append("pokemon")
    if "one piece" in alltext or "onepiece" in alltext:
        score += 5
        reasons.append("one-piece")

    for term in DISCOVERY_WATCH_TERMS:
        if normalize_text(term) in alltext:
            score += 2
            reasons.append(term)
    for term in POKEMON_PRODUCT_TERMS:
        if normalize_text(term) in alltext:
            score += 1
    if any(x in normalize_text(title) for x in ("portfolio", "classeur", "binder", "album")):
        score += 4
        reasons.append("support-collection")
    if _extract_gtin_candidates(html):
        score += 1
        reasons.append("gtin")

    return score, list(dict.fromkeys(reasons))

def _discovery_line_key(line):
    parts = [x.strip() for x in line.split("|")]
    if len(parts) < 3 or not parts[1].startswith(("http://", "https://")):
        return None
    return parts[1].rstrip("/")

def _load_discovery_queue():
    queue = {}
    try:
        text = DISCOVERY_FILE.read_text(encoding="utf-8-sig")
    except FileNotFoundError:
        return []
    except OSError:
        return []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = [x.strip() for x in line.split("|")]
        if len(parts) < 3 or not parts[1].startswith(("http://", "https://")):
            continue
        name, url = parts[0], parts[1].rstrip("/")
        price = parse_price(parts[2])
        retailer = ""
        for part in parts[3:]:
            if part.lower().startswith("enseigne="):
                retailer = part.split("=", 1)[1].strip()
                break
        queue[url] = {
            "name": name, "url": url, "reference_price": price,
            "reference_source": retailer, "retailer": retailer,
        }
    return list(queue.values())

def _write_discovery_queue(items):
    rows = [
        "# Journal des produits découverts automatiquement",
        "# Nom | URL | prix ou PRIX_INCONNU | découverte | enseigne",
    ]
    stamp = datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")
    for item in items:
        price = item.get("reference_price")
        price_text = f"{float(price):.2f}" if price is not None else "PRIX_INCONNU"
        retailer = item.get("reference_source") or item.get("retailer") or "?"
        discovered_at = item.get("discovered_at") or stamp
        if isinstance(discovered_at, (int, float)):
            discovered_at = datetime.fromtimestamp(discovered_at).astimezone().strftime("%Y-%m-%d %H:%M:%S %z")
        rows.append(f"{item.get('name','Produit découvert')} | {item['url'].rstrip('/')} | {price_text} | découverte={discovered_at} | enseigne={retailer}")
    try:
        DISCOVERY_FILE.write_text("\n".join(rows) + "\n", encoding="utf-8")
    except OSError as exc:
        print(f"! impossible d'écrire discovered_products.txt: {exc}")

def _append_discovery_log(items):
    if not items:
        return 0
    queue = _load_discovery_queue()
    by_url = {x["url"].rstrip("/"): x for x in queue if x.get("url")}
    added = 0
    for item in items:
        url = (item.get("url") or "").rstrip("/")
        if not url:
            continue
        old = by_url.get(url)
        if old is None:
            item = dict(item)
            item.setdefault("discovered_at", time.time())
            by_url[url] = item
            added += 1
        else:
            # Mise à jour du prix/enseigne si la découverte devient plus complète.
            for key in ("name", "reference_price", "reference_source", "retailer"):
                if item.get(key) is not None:
                    old[key] = item[key]
    _write_discovery_queue(list(by_url.values()))
    return added

def _append_products_txt(items):
    if not items or not AUTO_ADD_DISCOVERED:
        return 0
    try:
        current = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        current = ""
    existing = set()
    for line in current.splitlines():
        m = LINE_RE.match(line.strip())
        if m:
            existing.add(m.group(2).rstrip("/"))
    additions = []
    promoted_urls = set()
    for item in items:
        url = (item.get("url") or "").rstrip("/")
        price = item.get("reference_price")
        if not url or price is None or url in existing:
            if url in existing:
                promoted_urls.add(url)
            continue
        try:
            price = float(price)
        except (TypeError, ValueError):
            continue
        if price <= 0:
            continue
        name = str(item.get("name") or "Produit découvert").replace("|", "-").strip()
        additions.append(f"{name} | {url} | {price:.2f}")
        existing.add(url)
        promoted_urls.add(url)
    if not additions:
        return 0
    sep = "\n" if current and not current.endswith("\n") else ""
    try:
        PRODUCTS_FILE.write_text(
            current + sep + "\n# Produits découverts automatiquement — prix enseigne\n" +
            "\n".join(additions) + "\n", encoding="utf-8"
        )
        # Retire les produits désormais actifs de la file de découverte.
        queue = [x for x in _load_discovery_queue() if x.get("url", "").rstrip("/") not in promoted_urls]
        _write_discovery_queue(queue)
        print(f"+ {len(additions)} nouveau(x) produit(s) ajouté(s) automatiquement à products.txt")
        return len(additions)
    except OSError as exc:
        print(f"! impossible d'ajouter automatiquement à products.txt: {exc}")
        return 0

def retry_discovered_prices():
    """Retente les prix des découvertes conservées sans prix."""
    queue = _load_discovery_queue()
    pending = [x for x in queue if x.get("reference_price") is None]
    if not pending:
        return []
    promoted = []
    now = time.time()
    for item in pending:
        url = item.get("url", "").rstrip("/")
        if not url:
            continue
        retailer = item.get("reference_source") or item.get("retailer") or ""
        if not retailer:
            host = urlparse(url).netloc.lower().lstrip("www.")
            retailer = DISCOVERY_RETAILERS.get(host, ("", ()))[0]
        try:
            html = _fetch_once(url, DISCOVERY_TIMEOUT)
            title = _product_title(html, url)
            if _is_explicitly_english_tcg(title, url, html):
                continue
            price = _reference_price_from_retailer(html, retailer) if retailer else extract_price(html)
        except Exception as exc:
            if DISCOVERY_LOG_ALL_CANDIDATES:
                print(f"    ! retry prix impossible {url}: {exc}")
            continue
        if price is not None:
            item["reference_price"] = price
            item["price"] = price
            item["reference_source"] = retailer
            promoted.append(item)
    if promoted:
        _append_discovery_log(promoted)
        _append_products_txt(promoted)
    return promoted

def discover_via_search_engines(products):
    if not SEARCH_DISCOVERY_ENABLED:
        return []

    known = {p["url"].rstrip("/") for p in products}
    discovered = []
    per_host = {domain: 0 for domain in DISCOVERY_RETAILERS}

    for domain, (retailer, families) in DISCOVERY_RETAILERS.items():
        if per_host[domain] >= DISCOVERY_MAX_PER_HOST:
            continue
        queries = _discovery_queries(domain)[:max(1, SEARCH_QUERIES_PER_HOST)]
        for query in queries:
            if per_host[domain] >= DISCOVERY_MAX_PER_HOST:
                break
            print(f"  🔎 {retailer}: {query[:150]}")
            for url in _search_engine_urls(query):
                if per_host[domain] >= DISCOVERY_MAX_PER_HOST:
                    break
                clean = _clean_candidate_url(url)
                if not clean or clean in known:
                    continue
                parsed = urlparse(clean)
                host = parsed.netloc.lower().split(":")[0].lstrip("www.")
                if host != domain:
                    continue
                try:
                    html = _fetch_once(clean, DISCOVERY_TIMEOUT)
                except Exception as exc:
                    if DISCOVERY_LOG_ALL_CANDIDATES:
                        print(f"    ! échec {clean}: {exc}")
                    continue
                title = _product_title(html, clean)
                if _is_explicitly_english_tcg(title, clean, html):
                    if DISCOVERY_LOG_ALL_CANDIDATES:
                        print(f"    - rejet anglais: {title[:100]}")
                    continue
                pokemon_ok = is_relevant_pokemon_candidate(title, clean, html)
                onepiece_ok = is_relevant_onepiece_candidate(title, clean, html)
                if not (pokemon_ok or onepiece_ok):
                    if DISCOVERY_LOG_ALL_CANDIDATES:
                        print(f"    - rejet: {title[:100]}")
                    continue
                status, source = classify(html)
                score, reasons = _score_candidate(retailer, title, clean, html)
                if score < 6:
                    continue
                reference_price = _reference_price_from_retailer(html, retailer)
                item = {
                    "name": f"{retailer} - {title}", "url": clean,
                    "reference_price": reference_price,
                    "reference_source": retailer, "retailer": retailer,
                    "price": reference_price, "status": status, "source": source,
                    "discovery_score": score, "discovery_reasons": reasons,
                    "discovered_at": time.time(),
                }
                discovered.append(item)
                known.add(clean)
                per_host[domain] += 1
                price_text = f"{reference_price:.2f} €" if reference_price is not None else "prix en attente"
                print(f"    ✅ DÉCOUVERTE [{retailer}] {title[:120]} | {price_text} | score={score}")

    if not discovered:
        print("  ℹ️ aucune nouvelle fiche produit découverte.")
        return []
    logged = _append_discovery_log(discovered)
    print(f"  📝 {logged} découverte(s) journalisée(s) dans discovered_products.txt")
    added = _append_products_txt(discovered)
    if not AUTO_ADD_DISCOVERED:
        print("  ℹ️ AUTO_ADD_DISCOVERED=0 : produits détectés mais non ajoutés à products.txt")
    elif not added:
        print("  ℹ️ aucune nouvelle URL à ajouter à products.txt (prix potentiellement en attente)")
    return discovered

def activate_new_discoveries(state, products, discovered):
    if not discovered:
        return products
    products[:] = load_products()
    discovered_urls = {x.get("url", "").rstrip("/") for x in discovered}
    for p in products:
        if p["url"].rstrip("/") in discovered_urls:
            entry = state["products"].setdefault(p["url"], new_entry())
            entry["name"], entry["url"], entry["next_check"] = p["name"], p["url"], 0

    if DISCOVERY_IMMEDIATE_CHECK:
        priority = [
            p for p in products
            if p["url"].rstrip("/") in discovered_urls and
            any(x in normalize_text(f"{p['name']} {p['url']}") for x in DROP_PRIORITY_TERMS)
        ]
        if priority:
            print(f"⚡ {len(priority)} nouvelle(s) cible(s) prioritaire(s) : vérification immédiate")
            run_due(state, priority, time.monotonic() + min(RUN_DEADLINE, 60))
            save_state(state)
    return products

def discover_new_products(products, run_catalog=True):
    """Découverte hybride V15 : file persistante + catalogue direct + Google/Bing."""
    discovered = []
    promoted = retry_discovered_prices()
    discovered.extend(promoted)
    # Recharger après promotion éventuelle.
    try:
        products[:] = load_products()
    except Exception:
        pass
    if run_catalog:
        discovered.extend(discover_via_catalogs(products))
    discovered.extend(discover_via_search_engines(list(products) + discovered))
    # Journal + ajout après catalogue direct également.
    if discovered:
        _append_discovery_log(discovered)
        _append_products_txt(discovered)
    unique, seen = [], set()
    for item in discovered:
        key = item.get("url", "").rstrip("/")
        if key and key not in seen:
            seen.add(key); unique.append(item)
    return unique

# ---------------------------------------------------------------------------
# PRIX DE RÉFÉRENCE
# ---------------------------------------------------------------------------

def _find_official_price_for_product(name, source_url, source_html):
    prices, seen_urls = [], set()
    queries = _candidate_product_queries(name, source_html)
    for domain, (retailer, _families) in DISCOVERY_RETAILERS.items():
        for base_query in queries[:3]:
            query = f"site:{domain} {base_query}"
            for url in _search_engine_urls(query)[:SEARCH_RESULTS_PER_QUERY]:
                parsed = urlparse(url)
                if parsed.netloc.lower().split(":")[0].lstrip("www.") != domain:
                    continue
                clean = _clean_candidate_url(url)
                if not clean or clean in seen_urls:
                    continue
                seen_urls.add(clean)
                try:
                    html = _fetch_once(clean, DISCOVERY_TIMEOUT)
                except Exception:
                    continue
                title_raw = _product_title(html, clean)
                if _is_explicitly_english_tcg(title_raw, clean, html):
                    continue
                title = title_raw.lower()
                src_title = _product_title(source_html, source_url).lower()
                tokens = [t for t in re.findall(r"[a-z0-9éèêàùûôîïç]+", src_title) if len(t) >= 4]
                overlap = sum(1 for t in set(tokens) if t in title)
                ean_match = bool(set(_extract_gtin_candidates(source_html)) & set(_extract_gtin_candidates(html)))
                if not ean_match and overlap < 3:
                    continue
                price = _reference_price_from_retailer(html, retailer)
                if price is not None:
                    prices.append((price, retailer, clean))
    return min(prices, key=lambda x: x[0]) if prices else None

def refresh_existing_reference_prices(products):
    if not AUTO_REFRESH_PRICES:
        return 0
    changed, rows = 0, []
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
            rows.append(raw)
            continue
        hay = normalize_text(name + " " + url)
        if not any(x in hay for x in ("pokemon", "pokémon", "one piece", "onepiece", "op-17", "op-18", "op-19", "ts-03", "ts03", "eb-")):
            rows.append(raw)
            continue
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
        PRODUCTS_FILE.write_text("\n".join(rows) + "\n", encoding="utf-8")
    return changed

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

    parser = argparse.ArgumentParser(description="Surveillance de stock Pokémon / One Piece avec découverte automatique.")
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--fast", action="store_true")
    parser.add_argument("--duration", type=int, default=300)
    parser.add_argument("--interval", type=int, default=20)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--physical", action="store_true")
    parser.add_argument("--discover-only", action="store_true",
                        help="lance uniquement la découverte automatique")
    args = parser.parse_args()

    if args.test:
        sys.exit(0 if notify("Test bot Pokémon", "Les notifications ntfy fonctionnent.",
                             priority="3", tags="white_check_mark") else 1)

    purge_obsolete_products()

    try:
        products = load_products()
    except RuntimeError as exc:
        print(f"! {exc}")
        sys.exit(2)

    state = load_state()

    if args.discover_only:
        try:
            newly = discover_new_products(products, run_catalog=True)
            if newly:
                activate_new_discoveries(state, products, newly)
            state["last_discovery"] = time.time()
            save_state(state)
        except Exception as exc:
            print(f"! découverte automatique en erreur: {exc}")
            traceback.print_exc()
            sys.exit(1)
        return

    if args.physical:
        for product in products:
            state["products"].setdefault(product["url"], new_entry())["next_check"] = 0
        safe_cycle(state, products)
        return

    last_price_refresh = state.get("last_price_refresh", 0)
    if AUTO_REFRESH_PRICES and (
        time.time() - last_price_refresh >= PRICE_REFRESH_HOURS * 3600 or args.once
    ):
        try:
            refresh_existing_reference_prices(products)
            products[:] = load_products()
            state["last_price_refresh"] = time.time()
            save_state(state)
        except Exception as exc:
            print(f"! recalcul des prix de référence en erreur: {exc}")

    if DISCOVERY_ENABLED:
        try:
            now = time.time()
            catalog_due = (now - float(state.get("last_catalog_discovery", 0) or 0) >= CATALOG_DISCOVERY_EVERY)
            newly = discover_new_products(products, run_catalog=catalog_due)
            if newly:
                activate_new_discoveries(state, products, newly)
            else:
                products[:] = load_products()
            state["last_discovery"] = now
            if catalog_due:
                state["last_catalog_discovery"] = now
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
                state["products"].setdefault(product["url"], new_entry())["next_check"] = 0
            safe_cycle(state, products)
            if DISCOVERY_ENABLED and time.time() - state.get("last_discovery", 0) >= min(DISCOVERY_EVERY, 300):
                try:
                    now = time.time()
                    catalog_due = now - float(state.get("last_catalog_discovery", 0) or 0) >= CATALOG_DISCOVERY_EVERY
                    newly = discover_new_products(products, run_catalog=catalog_due)
                    if newly:
                        activate_new_discoveries(state, products, newly)
                    else:
                        products[:] = load_products()
                    state["last_discovery"] = now
                    if catalog_due:
                        state["last_catalog_discovery"] = now
                    save_state(state)
                except Exception as exc:
                    print(f"! découverte automatique en erreur: {exc}")
            time.sleep(max(MIN_INTERVAL, args.interval) + random.uniform(0, 3))
        print("Mode rapide terminé.")
        return

    print(f"Bot V15 lancé — filtre prix +{PRICE_TOLERANCE_PCT:g}% | {len(products)} produits.")
    print("Découverte: catalogues directs + Google/Bing | TCG FR uniquement | TS-03/OP-17/OP-18 activés.")
    print("Ctrl+C pour arrêter.")

    try:
        while True:
            safe_cycle(state, products)
            if DISCOVERY_ENABLED and time.time() - state.get("last_discovery", 0) >= DISCOVERY_EVERY:
                try:
                    now = time.time()
                    catalog_due = now - float(state.get("last_catalog_discovery", 0) or 0) >= CATALOG_DISCOVERY_EVERY
                    newly = discover_new_products(products, run_catalog=catalog_due)
                    if newly:
                        activate_new_discoveries(state, products, newly)
                    else:
                        products[:] = load_products()
                    state["last_discovery"] = now
                    if catalog_due:
                        state["last_catalog_discovery"] = now
                    save_state(state)
                except Exception as exc:
                    print(f"! découverte automatique en erreur: {exc}")
            time.sleep(3)
    except KeyboardInterrupt:
        print("\nArrêt.")

if __name__ == "__main__":
    main()
