#!/usr/bin/env python3
"""
Bot de surveillance de stock PokÃ©mon / One Piece TCG - V2

Objectif :
- dÃ©tecter rapidement les changements de stock ;
- limiter les faux positifs ;
- notifier immÃ©diatement via ntfy ;
- rester compatible avec le products.txt existant ;
- ne pas automatiser le panier/checkout : l'achat reste manuel.

Format products.txt :
    Nom du produit | https://exemple.fr/produit

Variables d'environnement utiles :
    NTFY_TOPIC=...
    CHECK_EVERY=120
    FAST_INTERVAL=20
    REQUEST_TIMEOUT=12
    MAX_WORKERS=8
"""

import argparse
import gzip
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

def env_int(name, default, minimum=None):
    try:
        value = int(os.environ.get(name, default))
        return max(minimum, value) if minimum is not None else value
    except (TypeError, ValueError):
        return default

NTFY_TOPIC = (os.environ.get("NTFY_TOPIC") or "").strip()
CHECK_EVERY = env_int("CHECK_EVERY", 120, 20)
FAST_INTERVAL = env_int("FAST_INTERVAL", 20, 10)
FAST_DURATION = env_int("FAST_DURATION", 300, 30)
REQUEST_TIMEOUT = env_int("REQUEST_TIMEOUT", 12, 5)
FETCH_RETRIES = env_int("FETCH_RETRIES", 2, 0)
MAX_PAGE_BYTES = env_int("MAX_PAGE_BYTES", 3_500_000, 100_000)
MAX_WORKERS = env_int("MAX_WORKERS", 8, 1)
RUN_DEADLINE = env_int("RUN_DEADLINE", 180, 20)
HOST_DELAY_MIN = float(os.environ.get("HOST_DELAY_MIN", "0.5"))
HOST_DELAY_MAX = float(os.environ.get("HOST_DELAY_MAX", "1.5"))
WEAK_CONFIRMATIONS = env_int("WEAK_CONFIRMATIONS", 2, 1)
PROBLEM_ALERT_MINUTES = env_int("PROBLEM_ALERT_MINUTES", 20, 1)
HEARTBEAT_EVERY_HOURS = env_int("HEARTBEAT_EVERY_HOURS", 24, 0)
ALERT_COOLDOWN_HOURS = env_int("ALERT_COOLDOWN_HOURS", 6, 1)
ALERT_ON_PREORDER = os.environ.get("ALERT_ON_PREORDER", "1").lower() not in {"0", "false", "no"}

BASE_DIR = Path(__file__).resolve().parent
PRODUCTS_FILE = BASE_DIR / "products.txt"
STATE_FILE = BASE_DIR / "stock_state.json"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/128.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "fr-FR,fr;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept-Encoding": "gzip, deflate, br" if HAS_BROTLI else "gzip, deflate",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
}

TRANSIENT_HTTP = {408, 425, 429, 500, 502, 503, 504}

# DÃ©tection structurÃ©e : plus fiable que les mots-clÃ©s.
IN_KEYS = {
    "instock", "limitedavailability", "onlineonly", "instoreonly",
    "availablefororder", "in_stock", "available"
}
PRE_KEYS = {"preorder", "presale", "backorder", "pre_order"}
OUT_KEYS = {
    "outofstock", "soldout", "discontinued", "oos", "out_of_stock",
    "unavailable"
}

LD_RE = re.compile(
    r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
    re.I | re.S,
)
NEXT_DATA_RE = re.compile(
    r'<script[^>]+id=["\']__NEXT_DATA__["\'][^>]*>(.*?)</script>',
    re.I | re.S,
)
NUXT_RE = re.compile(
    r'<script[^>]+id=["\']__NUXT__["\'][^>]*>(.*?)</script>',
    re.I | re.S,
)

OG_RES = [
    re.compile(
        r'(?:product|og):availability["\']\s+content=["\']([^"\']+)["\']',
        re.I,
    ),
    re.compile(
        r'content=["\']([^"\']+)["\']\s+'
        r'(?:property|name)=["\'](?:product|og):availability["\']',
        re.I,
    ),
]

OUT_WORDS = (
    "Ã©puisÃ©", "epuise", "rupture de stock", "out of stock",
    "sold out", "indisponible", "plus disponible",
)
IN_WORDS = (
    "ajouter au panier", "add to cart", "ajouter Ã  la commande",
    "acheter maintenant", "disponible", "en stock",
)
PRE_WORDS = ("prÃ©commande", "precommande", "pre-order", "preorder")
BLOCK_WORDS = (
    "captcha", "access denied", "just a moment", "datadome",
    "verify you are human", "unusual traffic", "vÃ©rification de sÃ©curitÃ©",
    "robot check", "cf-chl",
)

# ---------------------------------------------------------------------------
# OUTILS
# ---------------------------------------------------------------------------

class ConfigError(Exception):
    pass


class FetchError(Exception):
    def __init__(self, message, transient=False, status_code=None):
        super().__init__(message)
        self.transient = transient
        self.status_code = status_code


def now_ts():
    return time.time()


def norm(value):
    return re.sub(r"[^a-z0-9_]", "", str(value).lower().replace("-", "_"))


def flatten(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from flatten(value)
    elif isinstance(node, list):
        for value in node:
            yield from flatten(value)


def status_from_value(value):
    value = norm(value)
    if value in IN_KEYS or value.endswith("instock"):
        return "in"
    if value in PRE_KEYS or value.endswith("preorder"):
        return "preorder"
    if value in OUT_KEYS or value.endswith("outofstock"):
        return "out"
    return None


def http_message(code):
    messages = {
        403: "HTTP 403 : accÃ¨s refusÃ© par le site",
        404: "HTTP 404 : page introuvable",
        429: "HTTP 429 : trop de requÃªtes",
        500: "HTTP 500 : erreur serveur",
        502: "HTTP 502 : passerelle",
        503: "HTTP 503 : service indisponible",
        504: "HTTP 504 : dÃ©lai serveur dÃ©passÃ©",
    }
    return messages.get(code, f"HTTP {code}")


# ---------------------------------------------------------------------------
# RÃ‰SEAU
# ---------------------------------------------------------------------------

def build_opener():
    proxy = (
        os.environ.get("HTTPS_PROXY")
        or os.environ.get("HTTP_PROXY")
        or os.environ.get("https_proxy")
        or os.environ.get("http_proxy")
    )
    if proxy:
        return urllib.request.build_opener(
            urllib.request.ProxyHandler({"http": proxy, "https": proxy})
        )
    return urllib.request.build_opener()


OPENER = build_opener()


def decode_body(raw, encoding):
    enc = (encoding or "").lower().strip()
    try:
        if enc == "gzip":
            return gzip.decompress(raw)
        if enc == "deflate":
            try:
                return zlib.decompress(raw)
            except zlib.error:
                return zlib.decompress(raw, -zlib.MAX_WBITS)
        if enc == "br":
            if not HAS_BROTLI:
                raise FetchError("page compressÃ©e en Brotli : installe le paquet 'brotli'")
            return brotli.decompress(raw)
        if enc not in ("", "identity"):
            raise FetchError(f"encodage non gÃ©rÃ© : {enc}")
        return raw
    except FetchError:
        raise
    except Exception as exc:
        raise FetchError(f"dÃ©compression impossible : {exc}")


def fetch_once(url):
    req = urllib.request.Request(url, headers=HEADERS, method="GET")
    try:
        with OPENER.open(req, timeout=REQUEST_TIMEOUT) as response:
            raw = response.read(MAX_PAGE_BYTES + 1)
            if len(raw) > MAX_PAGE_BYTES:
                raise FetchError(f"page trop volumineuse (> {MAX_PAGE_BYTES} octets)")
            content = decode_body(raw, response.headers.get("Content-Encoding"))
            charset = response.headers.get_content_charset() or "utf-8"
            return content.decode(charset, errors="replace"), response.headers
    except urllib.error.HTTPError as exc:
        raise FetchError(
            http_message(exc.code),
            transient=exc.code in TRANSIENT_HTTP,
            status_code=exc.code,
        )
    except urllib.error.URLError as exc:
        raise FetchError(f"rÃ©seau : {exc.reason}", transient=True)
    except (http.client.HTTPException, TimeoutError, OSError) as exc:
        raise FetchError(f"rÃ©seau : {exc.__class__.__name__}", transient=True)


def fetch(url):
    last = None
    for attempt in range(FETCH_RETRIES + 1):
        try:
            return fetch_once(url)
        except FetchError as exc:
            last = exc
            if not exc.transient or attempt >= FETCH_RETRIES:
                raise
            # Backoff exponentiel + jitter. Un 429 doit ralentir plutÃ´t que marteler.
            delay = min(12, 1.5 * (2 ** attempt) + random.uniform(0, 1.0))
            time.sleep(delay)
    raise last


# ---------------------------------------------------------------------------
# DÃ‰TECTION
# ---------------------------------------------------------------------------

def parse_json_script(regex, html):
    results = []
    for match in regex.finditer(html):
        raw = match.group(1).strip()
        try:
            results.append(json.loads(raw))
        except (ValueError, TypeError):
            continue
    return results


def structured_statuses(html):
    statuses = []

    for data in parse_json_script(LD_RE, html):
        for node in flatten(data):
            if not isinstance(node, dict):
                continue
            for key in ("availability", "availabilityStatus"):
                value = node.get(key)
                if isinstance(value, str):
                    status = status_from_value(value)
                    if status:
                        statuses.append(("schema", status))

            offers = node.get("offers")
            if isinstance(offers, dict):
                value = offers.get("availability")
                if isinstance(value, str):
                    status = status_from_value(value)
                    if status:
                        statuses.append(("schema", status))

    for regex, source in ((NEXT_DATA_RE, "nextdata"), (NUXT_RE, "nuxt")):
        for data in parse_json_script(regex, html):
            for node in flatten(data):
                if not isinstance(node, dict):
                    continue

                for key in ("availability", "availabilityStatus"):
                    value = node.get(key)
                    if isinstance(value, str):
                        status = status_from_value(value)
                        if status:
                            statuses.append((source, status))

                for key in ("inStock", "isAvailable", "available"):
                    value = node.get(key)
                    if isinstance(value, bool):
                        statuses.append((source, "in" if value else "out"))

                for key in ("stockQuantity", "quantity", "inventory"):
                    value = node.get(key)
                    if isinstance(value, (int, float)):
                        statuses.append((source, "in" if value > 0 else "out"))

    for rx in OG_RES:
        for value in rx.findall(html):
            status = status_from_value(value)
            if status:
                statuses.append(("meta", status))

    return statuses


def visible_text(html):
    # On retire scripts/styles pour Ã©viter qu'un texte de debug ou une librairie
    # contenant "add to cart" crÃ©e un faux positif.
    text = re.sub(r"<script\b[^>]*>.*?</script>", " ", html, flags=re.I | re.S)
    text = re.sub(r"<style\b[^>]*>.*?</style>", " ", text, flags=re.I | re.S)
    text = re.sub(r"<noscript\b[^>]*>.*?</noscript>", " ", text, flags=re.I | re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", text).lower()


def classify(html):
    low = html.lower()

    # Protection anti-bot : prioritÃ© Ã  la sÃ©curitÃ© pour Ã©viter de conclure
    # "hors stock" ou "en stock" sur une page de challenge.
    block_hits = sum(1 for word in BLOCK_WORDS if word in low)
    if block_hits >= 2 or any(x in low for x in ("<title>access denied", "captcha-container")):
        return "blocked", "protection", 0.99

    structured = structured_statuses(html)

    # On exige plusieurs signaux concordants pour les donnÃ©es faibles.
    counts = {"in": 0, "preorder": 0, "out": 0}
    strong = {"in": 0, "preorder": 0, "out": 0}

    for source, status in structured:
        counts[status] += 1
        if source in {"schema", "meta"}:
            strong[status] += 1

    for status in ("in", "preorder", "out"):
        if strong[status] >= 1:
            return status, "schema", 0.98

    # Plusieurs donnÃ©es structurÃ©es identiques : confirmation raisonnable.
    ranked = sorted(counts.items(), key=lambda item: item[1], reverse=True)
    if ranked[0][1] >= 2 and ranked[0][1] > ranked[1][1]:
        return ranked[0][0], "framework", 0.90

    text = visible_text(html)

    out_hits = sum(text.count(word) for word in OUT_WORDS)
    in_hits = sum(text.count(word) for word in IN_WORDS)
    pre_hits = sum(text.count(word) for word in PRE_WORDS)

    # Une indication "hors stock" est prioritaire seulement si aucun signal
    # d'achat fort n'est prÃ©sent.
    if in_hits == 0 and out_hits > 0:
        return "out", "keywords", 0.65

    if in_hits > 0 and pre_hits > 0:
        return "preorder", "keywords", 0.60

    if in_hits > 0:
        return "in", "keywords", 0.60

    if out_hits > 0:
        return "out", "keywords", 0.60

    return "unknown", "none", 0.0


# ---------------------------------------------------------------------------
# PRODUITS / Ã‰TAT
# ---------------------------------------------------------------------------

LINE_RE = re.compile(r"^(.+?)\s*\|\s*(https?://\S+)\s*$")


def load_products():
    try:
        raw = PRODUCTS_FILE.read_text(encoding="utf-8-sig")
    except FileNotFoundError:
        raise ConfigError("products.txt est introuvable Ã  cÃ´tÃ© du script.")
    except OSError as exc:
        raise ConfigError(f"products.txt illisible : {exc}")

    products = []
    seen = set()

    for number, line in enumerate(raw.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue

        match = LINE_RE.match(line)
        if not match:
            print(f"! products.txt ligne {number} ignorÃ©e : format 'Nom | URL' attendu")
            continue

        name, url = match.group(1).strip(), match.group(2).strip()
        if url in seen:
            continue

        seen.add(url)
        products.append((name, url))

    if not products:
        raise ConfigError("products.txt ne contient aucun produit valide.")

    return products


def new_entry():
    return {
        "status": None,
        "alerted": False,
        "weak_hits": 0,
        "problem_since": 0.0,
        "problem_alerted": False,
        "last_check": 0.0,
        "last_source": "",
        "last_confidence": 0.0,
        "last_error": "",
        "consecutive_errors": 0,
    }


def new_state():
    return {
        "version": 2,
        "products": {},
        "last_heartbeat": 0.0,
        "last_crash_alert": 0.0,
        "last_config_alert": 0.0,
    }


def load_state():
    state = new_state()
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return state
    except Exception as exc:
        print(f"! Ã©tat illisible ({exc.__class__.__name__}), remise Ã  zÃ©ro.")
        return state

    if not isinstance(data, dict):
        return state

    for key in ("last_heartbeat", "last_crash_alert", "last_config_alert"):
        if isinstance(data.get(key), (int, float)):
            state[key] = float(data[key])

    products = data.get("products")
    if isinstance(products, dict):
        for url, old in products.items():
            entry = new_entry()
            if isinstance(old, dict):
                for key in entry:
                    if key in old:
                        entry[key] = old[key]
            try:
                entry["weak_hits"] = int(entry["weak_hits"])
                entry["consecutive_errors"] = int(entry["consecutive_errors"])
                entry["problem_since"] = float(entry["problem_since"])
                entry["last_check"] = float(entry["last_check"])
            except (TypeError, ValueError):
                entry = new_entry()
            state["products"][str(url)] = entry

    return state


def save_state(state):
    try:
        payload = json.dumps(state, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        tmp = STATE_FILE.with_suffix(".tmp")
        tmp.write_text(payload, encoding="utf-8")
        os.replace(tmp, STATE_FILE)
    except Exception as exc:
        print(f"! impossible d'Ã©crire l'Ã©tat : {exc}")


# ---------------------------------------------------------------------------
# NOTIFICATIONS
# ---------------------------------------------------------------------------

def notify(title, message, url="", priority="5", tags="rotating_light"):
    if not NTFY_TOPIC:
        print("  ! NTFY_TOPIC n'est pas configurÃ©.")
        return False

    endpoint = "https://ntfy.sh/" + urllib.parse.quote(NTFY_TOPIC, safe="")
    headers = {
        "Title": title[:200],
        "Priority": str(priority),
        "Tags": tags,
    }
    if url:
        headers["Click"] = url

    request = urllib.request.Request(
        endpoint,
        data=message[:3500].encode("utf-8"),
        headers=headers,
        method="POST",
    )

    try:
        with urllib.request.urlopen(request, timeout=10) as response:
            response.read()
        print("  -> notification envoyÃ©e")
        return True
    except Exception as exc:
        print(f"  ! notification impossible : {exc}")
        return False


def alert_limited(state, key, title, message):
    if now_ts() - state.get(key, 0) >= ALERT_COOLDOWN_HOURS * 3600:
        if notify(title, message, priority="4", tags="warning"):
            state[key] = now_ts()


# ---------------------------------------------------------------------------
# VÃ‰RIFICATION
# ---------------------------------------------------------------------------

def check_one(name, url):
    result = {
        "name": name,
        "url": url,
        "status": None,
        "source": None,
        "confidence": 0.0,
        "error": None,
        "http_status": None,
    }

    try:
        html, headers = fetch(url)
        status, source, confidence = classify(html)
        result.update(status=status, source=source, confidence=confidence)
        return result
    except FetchError as exc:
        result["error"] = str(exc)
        result["http_status"] = exc.status_code
        return result
    except Exception as exc:
        result["error"] = f"{exc.__class__.__name__}: {str(exc)[:100]}"
        return result


def fetch_all(products, deadline):
    # Un thread par domaine : plusieurs boutiques sont surveillÃ©es en parallÃ¨le,
    # mais on Ã©vite de marteler le mÃªme domaine avec plusieurs threads.
    groups = {}
    for name, url in products:
        host = urlparse(url).netloc.lower()
        groups.setdefault(host, []).append((name, url))

    results = {}

    def group_worker(items):
        local = []
        for index, item in enumerate(items):
            if time.monotonic() >= deadline:
                name, url = item
                local.append({
                    "name": name, "url": url, "status": None, "source": None,
                    "confidence": 0.0, "error": "tour terminÃ©", "http_status": None,
                    "skipped": True,
                })
                continue

            if index:
                time.sleep(random.uniform(HOST_DELAY_MIN, HOST_DELAY_MAX))

            local.append(check_one(*item))
        return local

    worker_count = min(MAX_WORKERS, max(1, len(groups
