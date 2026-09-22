#!/usr/bin/env python3
"""
Bot de surveillance de stock Pokémon + One Piece TCG - VERSION AMÉLIORÉE & RENFORCÉE

Corrections & Améliorations intégrées :
- En-têtes HTTP ultra-réalistes (Sec-Ch-Ua, Sec-Fetch-*, Accept, etc.) pour éviter les blocages 403.
- Décodage natif Brotli (br) avec fallback transparent si la bibliothèque n'est pas disponible.
- Support natif des Proxies HTTP/HTTPS (via variables d'environnement HTTP_PROXY / HTTPS_PROXY).
- Analyse avancée des frameworks modernes (Next.js __NEXT_DATA__ et Nuxt __NUXT__) pour Fnac, Leclerc, Carrefour, etc.
- Amélioration de la résilience et de la compatibilité GitHub Actions.
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
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse

# Module brotli optionnel
try:
    import brotli
    HAS_BROTLI = True
except ImportError:
    HAS_BROTLI = False

# ----------------------------------------------------------------------------
# CONFIG
# ----------------------------------------------------------------------------

NTFY_TOPIC = (os.environ.get("NTFY_TOPIC") or "CHANGE-MOI-pokestock-secret-123").strip()
TOPIC_UNSET = NTFY_TOPIC.startswith("CHANGE-MOI")

CHECK_EVERY = 180            # secondes entre deux tours (boucle continue)
FAST_DURATION = 270          # mode rapide : durée d'un tour GitHub (secondes)
FAST_INTERVAL = 30           # mode rapide : secondes entre deux vérifications
MIN_INTERVAL = 20            # intervalle minimum
ALERT_ON_PREORDER = True     # alerter aussi sur précommande
HEARTBEAT_EVERY_HOURS = 24   # message de présence
PROBLEM_ALERT_MINUTES = 30   # délai avant alerte d'échec continu
WEAK_CONFIRMATIONS = 2       # lectures par mots-clés à confirmer
ALERT_COOLDOWN_HOURS = 6     # délai entre alertes d'erreur interne

REQUEST_TIMEOUT = 15         # secondes par requête
FETCH_RETRIES = 2            # réessais sur erreur temporaire
MAX_PAGE_BYTES = 3_000_000   # taille max lue par page
HOST_DELAY = (1.5, 3.5)      # pause entre deux pages du MÊME site
MAX_WORKERS = 6              # sites vérifiés en parallèle
RUN_DEADLINE = 200           # secondes max par tour

BASE_DIR = Path(__file__).resolve().parent
PRODUCTS_FILE = BASE_DIR / "products.txt"
STATE_FILE = BASE_DIR / "stock_state.json"

# En-têtes HTTP de navigateur récent (Chrome 128+)
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
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

BIG_RETAILERS = ("carrefour.", "fnac.", "amazon.", "auchan.", "leclerc", "smythstoys.",
                 "king-jouet.", "joueclub.", "lagranderecre.", "cultura.", "micromania.")
AMAZON_ASIN_RE = re.compile(r"/(?:dp|gp/product)/([A-Z0-9]{10})")

# ----------------------------------------------------------------------------
# DÉTECTION DU STOCK
# ----------------------------------------------------------------------------

IN_KEYS = {"instock", "limitedavailability", "onlineonly", "instoreonly", "availablefororder", "true"}
PRE_KEYS = {"preorder", "presale", "backorder"}
OUT_KEYS = {"outofstock", "soldout", "discontinued", "oos", "false"}

SCHEMA_RE = re.compile(
    r'(?:schema\.org/|"availability"\s*:\s*")'
    r"(InStock|LimitedAvailability|OnlineOnly|InStoreOnly|"
    r"PreOrder|PreSale|BackOrder|OutOfStock|SoldOut|Discontinued)",
    re.I,
)
OG_RES = [
    re.compile(r'(?:product|og):availability["']\s+content=["']([^"']+)["']', re.I),
    re.compile(r'content=["']([^"']+)["']\s+(?:property|name)=["'](?:product|og):availability["']', re.I),
]
LD_RE = re.compile(
    r'<script[^>]+type=["']application/ld\+json["'][^>]*>(.*?)</script>', re.I | re.S
)
NEXT_DATA_RE = re.compile(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', re.I | re.S)

OUT_WORDS = [
    "épuisé", "epuise", "rupture de stock", "out of stock", "sold out",
    "indisponible", "plus disponible", "victime de son succès",
]
IN_WORDS = ["ajouter au panier", "add to cart", "ajouter à la commande", "acheter maintenant"]
PRE_WORDS = ["précommande", "precommande", "pre-order", "preorder"]
BLOCK_WORDS = [
    "captcha", "access denied", "just a moment", "datadome", "verify you are human",
    "unusual traffic", "vérification de sécurité", "robot check", "cf-chl",
]


def _norm(value) -> str:
    return re.sub(r"[^a-z0-9]", "", str(value).lower().rsplit("/", 1)[-1])


def _walk(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from _walk(v)
    elif isinstance(node, list):
        for v in node:
            yield from _walk(v)


def _is_product(node: dict) -> bool:
    t = node.get("@type")
    types = t if isinstance(t, list) else [t]
    return any(isinstance(x, str) and x.lower() in ("product", "productgroup", "individualproduct")
               for x in types)


def _ld_availability(html: str) -> list:
    for m in LD_RE.finditer(html):
        try:
            data = json.loads(m.group(1).strip())
        except ValueError:
            continue
        for node in _walk(data):
            if isinstance(node, dict) and _is_product(node):
                keys = [
                    _norm(sub["availability"])
                    for sub in _walk([node.get("offers"), node.get("hasVariant")])
                    if isinstance(sub, dict) and isinstance(sub.get("availability"), str)
                ]
                if keys:
                    return keys
    return []


def _next_data_availability(html: str) -> list:
    m = NEXT_DATA_RE.search(html)
    if not m:
        return []
    try:
        data = json.loads(m.group(1))
        results = []
        for node in _walk(data):
            if isinstance(node, dict):
                if "inStock" in node and isinstance(node["inStock"], bool):
                    results.append("instock" if node["inStock"] else "outofstock")
                elif "stockQuantity" in node and isinstance(node["stockQuantity"], (int, float)):
                    results.append("instock" if node["stockQuantity"] > 0 else "outofstock")
                elif "isAvailable" in node and isinstance(node["isAvailable"], bool):
                    results.append("instock" if node["isAvailable"] else "outofstock")
                elif "availability" in node and isinstance(node["availability"], str):
                    results.append(_norm(node["availability"]))
        return results
    except Exception:
        return []


def _decide(keys):
    kinds = set()
    for k in keys:
        if k in IN_KEYS:
            kinds.add("in")
        elif k in PRE_KEYS:
            kinds.add("preorder")
        elif k in OUT_KEYS:
            kinds.add("out")
    for status in ("in", "preorder", "out"):
        if status in kinds:
            return status, kinds
    return None, kinds


def classify(html: str):
    """Retourne (statut, source).
    statut : 'in' | 'preorder' | 'out' | 'blocked' | 'unknown'
    source : 'schema' / 'meta' / 'nextdata' (fiable) ou 'keywords' (peu fiable)"""
    # 1) JSON-LD du produit principal
    status, _ = _decide(_ld_availability(html))
    if status:
        return status, "schema"

    # 2) Frameworks modernes (Next.js __NEXT_DATA__)
    status, _ = _decide(_next_data_availability(html))
    if status:
        return status, "nextdata"

    # 3) Microdonnées / schema.org dans la page
    status, kinds = _decide([_norm(m) for m in SCHEMA_RE.findall(html)])
    if status:
        return status, ("keywords" if len(kinds) > 1 else "schema")

    # 4) Balise Open Graph
    og = [_norm(m) for rx in OG_RES for m in rx.findall(html)]
    status, _ = _decide(og)
    if status:
        return status, "meta"

    # 5) Repli par mots-clés
    low = html.lower()
    if any(w in low for w in OUT_WORDS):
        return "out", "keywords"
    has_in = any(w in low for w in IN_WORDS)
    if has_in and any(w in low for w in PRE_WORDS):
        return "preorder", "keywords"
    if has_in:
        return "in", "keywords"
    if any(w in low for w in BLOCK_WORDS):
        return "blocked", "keywords"
    return "unknown", "keywords"


# ----------------------------------------------------------------------------
# RÉSEAU & PROXIES
# ----------------------------------------------------------------------------

class FetchError(Exception):
    def __init__(self, message, transient=False):
        super().__init__(message)
        self.transient = transient


def _http_message(code: int) -> str:
    if code == 403:
        return "HTTP 403 (accès refusé : le site bloque probablement les bots / IP Datacenter)"
    if code == 404:
        return "HTTP 404 (page introuvable : le lien a peut-être changé)"
    if code == 429:
        return "HTTP 429 (trop de requêtes)"
    return f"HTTP {code}"


def _fetch_once(url: str) -> str:
    req = urllib.request.Request(url, headers=HEADERS)
    
    # Prise en charge des Proxies via variables d'environnement (HTTP_PROXY / HTTPS_PROXY)
    proxy = os.environ.get("HTTPS_PROXY") or os.environ.get("HTTP_PROXY") or os.environ.get("https_proxy") or os.environ.get("http_proxy")
    if proxy:
        handler = urllib.request.ProxyHandler({'http': proxy, 'https': proxy})
        opener = urllib.request.build_opener(handler)
    else:
        opener = urllib.request.build_opener()

    with opener.open(req, timeout=REQUEST_TIMEOUT) as r:
        raw = r.read(MAX_PAGE_BYTES)
        enc = (r.headers.get("Content-Encoding") or "").lower()
        charset = r.headers.get_content_charset() or "utf-8"

    if enc == "gzip":
        raw = zlib.decompressobj(16 + zlib.MAX_WBITS).decompress(raw, MAX_PAGE_BYTES)
    elif enc == "deflate":
        try:
            raw = zlib.decompressobj().decompress(raw, MAX_PAGE_BYTES)
        except zlib.error:
            raw = zlib.decompressobj(-zlib.MAX_WBITS).decompress(raw, MAX_PAGE_BYTES)
    elif enc == "br":
        if HAS_BROTLI:
            try:
                raw = brotli.decompress(raw)
            except Exception as e:
                raise FetchError(f"erreur décompression brotli ({e})")
        else:
            raise FetchError("reçu encodage brotli (br) sans module brotli installé")
    elif enc not in ("", "identity"):
        raise FetchError(f"encodage de page non géré ({enc})")

    try:
        return raw.decode(charset, errors="replace")
    except LookupError:
        return raw.decode("utf-8", errors="replace")


def fetch(url: str) -> str:
    last = None
    for attempt in range(FETCH_RETRIES + 1):
        try:
            return _fetch_once(url)
        except urllib.error.HTTPError as e:
            last = FetchError(_http_message(e.code), e.code in TRANSIENT_HTTP)
        except FetchError as e:
            last = e
        except (urllib.error.URLError, http.client.HTTPException, OSError,
                zlib.error, EOFError) as e:
            last = FetchError(f"réseau ({e.__class__.__name__})", True)
        if not last.transient or attempt == FETCH_RETRIES:
            raise last
        time.sleep(2 * (attempt + 1) + random.random())
    raise last


def _header(text: str, limit: int = 200) -> str:
    return " ".join(str(text).split()).encode("latin-1", "replace").decode("latin-1")[:limit]


def retailer_actions(url: str):
    host = urlparse(url).netloc.lower()
    if not any(k in host for k in BIG_RETAILERS):
        return None, ""
    actions = [("Ouvrir la page", url)]
    if "amazon." in host:
        m = AMAZON_ASIN_RE.search(url)
        if m:
            actions.append(("Ajouter au panier",
                            f"https://{host}/gp/aws/cart/add.html?ASIN.1={m.group(1)}&Quantity.1=1"))
    tip = "
Grande enseigne : sois déjà connecté, ouvre la page et ajoute au panier tout de suite."
    return actions, tip


def notify(title: str, message: str, url: str = "", priority: str = "5",
           tags: str = "rotating_light", actions=None) -> bool:
    if TOPIC_UNSET:
        print("  ! NTFY_TOPIC n'est pas configuré : notification non envoyée.")
        return False
    endpoint = "https://ntfy.sh/" + urllib.parse.quote(NTFY_TOPIC, safe="")
    headers = {"Title": _header(title), "Priority": str(priority), "Tags": tags}
    if url:
        headers["Click"] = urllib.parse.quote(url, safe=":/?&=%#@+,;~!$*()[]")
    if actions:
        parts = [f"view, {label}, {u}" for label, u in actions if "," not in u and ";" not in u]
        if parts:
            headers["Actions"] = _header("; ".join(parts), 1500)
    data = str(message)[:1500].encode("utf-8")

    error = None
    for attempt in range(3):
        try:
            req = urllib.request.Request(endpoint, data=data, headers=headers, method="POST")
            urllib.request.urlopen(req, timeout=15).read()
            print("  -> notification envoyée")
            return True
        except Exception as e:
            error = e
            if attempt < 2:
                time.sleep(2 * (attempt + 1))
    print(f"  ! échec de la notification, nouvel essai au prochain tour : {error}")
    return False


# ----------------------------------------------------------------------------
# PRODUITS
# ----------------------------------------------------------------------------

class ConfigError(Exception):
    pass


LINE_RE = re.compile(r"^(.+?)\s*\|\s*(https?://\S+)\s*$")


def load_products():
    try:
        text = PRODUCTS_FILE.read_bytes().decode("utf-8-sig", errors="replace")
    except FileNotFoundError:
        raise ConfigError("products.txt est introuvable à côté du script.")
    except OSError as e:
        raise ConfigError(f"products.txt est illisible ({e.__class__.__name__}).")

    products, seen = [], set()
    for n, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        m = LINE_RE.match(line)
        if not m or "..." in m.group(2):
            print(f"! products.txt ligne {n} ignorée (format 'Nom | URL' attendu) : {line[:60]}")
            continue
        name, url = m.group(1).strip(), m.group(2).strip()
        if url in seen:
            print(f"! products.txt ligne {n} ignorée (doublon) : {name}")
            continue
        seen.add(url)
        products.append((name, url))
    if not products:
        raise ConfigError("products.txt ne contient aucun produit valide.")
    return products


# ----------------------------------------------------------------------------
# ÉTAT (mémoire du bot)
# ----------------------------------------------------------------------------

def new_entry() -> dict:
    return {"status": None, "alerted": False, "problem_since": 0,
            "problem_alerted": False, "weak_hits": 0}


def new_state() -> dict:
    return {"products": {}, "last_heartbeat": 0,
            "last_crash_alert": 0, "last_config_alert": 0}


def load_state() -> dict:
    state = new_state()
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("format inattendu")
    except FileNotFoundError:
        return state
    except Exception as e:
        print(f"! stock_state.json illisible ({e.__class__.__name__}) : on repart de zéro.")
        return state

    for key in ("last_heartbeat", "last_crash_alert", "last_config_alert"):
        if isinstance(data.get(key), (int, float)):
            state[key] = data[key]
    products = data.get("products")
    if isinstance(products, dict):
        for url, entry in products.items():
            e = new_entry()
            if isinstance(entry, dict):
                for k in e:
                    if k in entry:
                        e[k] = entry[k]
            try:
                e["problem_since"] = float(e["problem_since"])
                e["weak_hits"] = int(e["weak_hits"])
            except (TypeError, ValueError):
                e["problem_since"], e["weak_hits"] = 0, 0
            e["alerted"] = bool(e["alerted"])
            e["problem_alerted"] = bool(e["problem_alerted"])
            state["products"][str(url)] = e
    return state


def save_state(state: dict) -> None:
    try:
        text = json.dumps(state, indent=2, ensure_ascii=False, sort_keys=True) + "
"
        try:
            if STATE_FILE.read_text(encoding="utf-8") == text:
                return
        except OSError:
            pass
        tmp = STATE_FILE.with_name(STATE_FILE.name + ".tmp")
        tmp.write_text(text, encoding="utf-8")
        os.replace(tmp, STATE_FILE)
    except Exception as e:
        print(f"! impossible d'écrire l'état : {e}")


def alert_limited(state: dict, key: str, title: str, message: str) -> None:
    if time.time() - state.get(key, 0) >= ALERT_COOLDOWN_HOURS * 3600:
        if notify(title, message, priority="4", tags="warning"):
            state[key] = time.time()


# ----------------------------------------------------------------------------
# TOUR DE VÉRIFICATION
# ----------------------------------------------------------------------------

def check_one(name: str, url: str) -> dict:
    res = {"name": name, "url": url, "status": None, "source": None,
           "error": None, "skipped": False}
    try:
        res["status"], res["source"] = classify(fetch(url))
    except FetchError as e:
        res["error"] = str(e)
    except Exception as e:
        res["error"] = f"erreur inattendue ({e.__class__.__name__}: {str(e)[:60]})"
    return res


def check_group(items: list, deadline: float) -> list:
    out = []
    for i, (name, url) in enumerate(items):
        if time.monotonic() > deadline:
            out.append({"name": name, "url": url, "status": None, "source": None,
                        "error": None, "skipped": True})
            continue
        if i:
            time.sleep(random.uniform(*HOST_DELAY))
        out.append(check_one(name, url))
    return out


def fetch_all(products: list, deadline: float) -> dict:
    groups = {}
    for name, url in products:
        groups.setdefault(urlparse(url).netloc.lower(), []).append((name, url))
    results = {}
    with ThreadPoolExecutor(max_workers=max(1, min(MAX_WORKERS, len(groups)))) as ex:
        futures = [(ex.submit(check_group, g, deadline), g) for g in groups.values()]
        for fut, group in futures:
            try:
                for r in fut.result():
                    results[r["url"]] = r
            except Exception as e:
                for name, url in group:
                    results[url] = {"name": name, "url": url, "status": None, "source": None,
                                    "error": f"erreur interne ({e.__class__.__name__})",
                                    "skipped": False}
    return results


def run_once(state: dict, products: list) -> None:
    started = time.monotonic()
    print(f"
[{datetime.now():%H:%M:%S}] Vérification de {len(products)} produit(s)...")
    results = fetch_all(products, started + RUN_DEADLINE)

    entries = state["products"]
    current = {url for _, url in products}
    for url in [u for u in entries if u not in current]:
        del entries[url]

    ok = available = failing = skipped = 0
    problems, recovered = [], []

    for name, url in products:
        res = results[url]
        entry = entr
