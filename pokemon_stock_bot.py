    #!/usr/bin/env python3
"""
Bot de surveillance de stock Pokémon + One Piece TCG - VERSION SOLIDE

Compatible avec tes fichiers actuels : products.txt, stock.yml, stock_state.json
et le secret GitHub NTFY_TOPIC. Rien d'autre à modifier.

CE QUI REND CETTE VERSION PLUS SOLIDE
- Ne plante pas : une erreur sur un site, un fichier abîmé ou un bug interne est
  attrapé. Le bot te prévient par ntfy au lieu d'échouer en silence.
- Réessais automatiques sur les erreurs temporaires (réseau, 429, 5xx),
  pour les pages comme pour les notifications ntfy.
- Sites vérifiés en parallèle (un site à la fois chacun) : un tour dure ~30 s
  au lieu d'1 min 30, et s'arrête proprement avant la limite du workflow.
- Détection plus fine : lit le produit principal de la page (JSON-LD), pas les
  produits "suggérés". Une détection peu fiable (mots-clés) doit être
  confirmée sur 2 tours avant d'alerter, pour éviter les fausses alertes.
- Sauvegarde de l'état atomique : un fichier jamais à moitié écrit. Il n'est
  réécrit que s'il change, donc moins de commits et moins de risques de conflit.
- Grandes enseignes (Carrefour, Fnac, Amazon, Leclerc, King Jouet...) : l'alerte de
  stock contient des boutons "Ouvrir la page" (et "Ajouter au panier" pour Amazon).
  Pas de boutons pour les boutiques indépendantes. Le bot n'ajoute RIEN au panier
  à ta place : un panier créé par un serveur ne serait pas le tien.
- Alertes ntfy : stock dispo, site en difficulté, site de nouveau lisible,
  message de survie quotidien, erreur interne, products.txt invalide.

UTILISATION
  python3 pokemon_stock_bot.py --once    un seul tour (mode normal, GitHub Actions)
  python3 pokemon_stock_bot.py --fast    MODE RAPIDE : vérifie toutes les ~30 s pendant
                                         ~4,5 min (un tour de GitHub Actions)
  python3 pokemon_stock_bot.py           boucle continue (PC, Termux)
  python3 pokemon_stock_bot.py --test    envoie une notification de test

MODE RAPIDE sur GitHub : Settings > Secrets and variables > Actions > onglet Variables >
New repository variable : nom FAST_MODE, valeur on. Supprime-la (ou mets off) pour
revenir au mode normal. Réserve-le aux jours de sortie.

Produits : dans products.txt, une ligne = "Nom | URL de la page du produit".
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

# ----------------------------------------------------------------------------
# CONFIG
# ----------------------------------------------------------------------------

# Le secret GitHub NTFY_TOPIC est lu ici. strip() retire les espaces / retours
# à la ligne parfois collés par erreur avec le secret.
NTFY_TOPIC = (os.environ.get("NTFY_TOPIC") or "CHANGE-MOI-pokestock-secret-123").strip()
TOPIC_UNSET = NTFY_TOPIC.startswith("CHANGE-MOI")

CHECK_EVERY = 180            # secondes entre deux tours (boucle continue uniquement)
FAST_DURATION = 270          # mode rapide : durée d'un tour GitHub (secondes)
FAST_INTERVAL = 30           # mode rapide : secondes entre deux vérifications
MIN_INTERVAL = 20            # jamais plus rapide (politesse, évite les blocages)
ALERT_ON_PREORDER = True     # alerter aussi quand la précommande s'ouvre
HEARTBEAT_EVERY_HOURS = 24   # message "je tourne" (0 pour désactiver)
PROBLEM_ALERT_MINUTES = 30   # minutes d'échec continu avant d'alerter (quelle que soit la cadence)
WEAK_CONFIRMATIONS = 2       # lectures "mots-clés" à confirmer avant d'alerter
ALERT_COOLDOWN_HOURS = 6     # délai mini entre deux alertes "erreur interne / config"

REQUEST_TIMEOUT = 15         # secondes par requête
FETCH_RETRIES = 2            # nouveaux essais sur erreur temporaire
MAX_PAGE_BYTES = 3_000_000   # taille max lue par page
HOST_DELAY = (1.5, 3.5)      # pause entre deux pages du MÊME site (politesse)
MAX_WORKERS = 6              # sites vérifiés en parallèle
RUN_DEADLINE = 200           # secondes max par tour (le workflow coupe à 300 s)

BASE_DIR = Path(__file__).resolve().parent
PRODUCTS_FILE = BASE_DIR / "products.txt"
STATE_FILE = BASE_DIR / "stock_state.json"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

TRANSIENT_HTTP = {408, 425, 429, 500, 502, 503, 504}

# Grandes enseignes : leur alerte de stock contient des boutons "1 tap" et un rappel
# (les boutiques indépendantes gardent l'alerte simple).
BIG_RETAILERS = ("carrefour.", "fnac.", "amazon.", "auchan.", "leclerc", "smythstoys.",
                 "king-jouet.", "joueclub.", "lagranderecre.", "cultura.", "micromania.")
AMAZON_ASIN_RE = re.compile(r"/(?:dp|gp/product)/([A-Z0-9]{10})")

# ----------------------------------------------------------------------------
# DÉTECTION DU STOCK
# ----------------------------------------------------------------------------

IN_KEYS = {"instock", "limitedavailability", "onlineonly", "instoreonly", "availablefororder"}
PRE_KEYS = {"preorder", "presale", "backorder"}
OUT_KEYS = {"outofstock", "soldout", "discontinued", "oos"}

SCHEMA_RE = re.compile(
    r'(?:schema\.org/|"availability"\s*:\s*")'
    r"(InStock|LimitedAvailability|OnlineOnly|InStoreOnly|"
    r"PreOrder|PreSale|BackOrder|OutOfStock|SoldOut|Discontinued)",
    re.I,
)
OG_RES = [
    re.compile(r'(?:product|og):availability["\']\s+content=["\']([^"\']+)["\']', re.I),
    re.compile(r'content=["\']([^"\']+)["\']\s+(?:property|name)=["\'](?:product|og):availability["\']', re.I),
]
LD_RE = re.compile(
    r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>', re.I | re.S
)

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
    """'https://schema.org/InStock' / 'in stock' -> 'instock'."""
    return re.sub(r"[^a-z]", "", str(value).lower().rsplit("/", 1)[-1])


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
    """Disponibilités du PRODUIT PRINCIPAL dans le JSON-LD (le premier produit trouvé)."""
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
    source : 'schema' / 'meta' (fiable) ou 'keywords' (peu fiable)"""
    # 1) JSON-LD du produit principal : la source la plus fiable
    status, _ = _decide(_ld_availability(html))
    if status:
        return status, "schema"

    # 2) Microdonnées / schema.org dans la page
    status, kinds = _decide([_norm(m) for m in SCHEMA_RE.findall(html)])
    if status:
        # Si la page mélange "en stock" et "épuisé" (produits suggérés), on se méfie
        return status, ("keywords" if len(kinds) > 1 else "schema")

    # 3) Balise Open Graph
    og = [_norm(m) for rx in OG_RES for m in rx.findall(html)]
    status, _ = _decide(og)
    if status:
        return status, "meta"

    # 4) Repli par mots-clés (peu fiable)
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
# RÉSEAU
# ----------------------------------------------------------------------------

class FetchError(Exception):
    def __init__(self, message, transient=False):
        super().__init__(message)
        self.transient = transient


def _http_message(code: int) -> str:
    if code == 403:
        return "HTTP 403 (accès refusé : le site bloque probablement les bots)"
    if code == 404:
        return "HTTP 404 (page introuvable : le lien a peut-être changé)"
    if code == 429:
        return "HTTP 429 (trop de requêtes)"
    return f"HTTP {code}"


def _fetch_once(url: str) -> str:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml",
            "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.5",
            "Accept-Encoding": "gzip",
        },
    )
    with urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT) as r:
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
    elif enc not in ("", "identity"):
        raise FetchError(f"encodage de page non géré ({enc})")

    try:
        return raw.decode(charset, errors="replace")
    except LookupError:  # charset inconnu
        return raw.decode("utf-8", errors="replace")


def fetch(url: str) -> str:
    """Télécharge une page avec réessais sur erreurs temporaires."""
    last = None
    for attempt in range(FETCH_RETRIES + 1):
        try:
            return _fetch_once(url)
        except urllib.error.HTTPError as e:  # avant OSError : HTTPError en hérite
            last = FetchError(_http_message(e.code), e.code in TRANSIENT_HTTP)
        except FetchError as e:
            last = e
        except (urllib.error.URLError, http.client.HTTPException, OSError,
                zlib.error, EOFError) as e:
            last = FetchError(f"réseau ({e.__class__.__name__})", True)
        if not last.transient or attempt == FETCH_RETRIES:
            raise last
        time.sleep(2 * (attempt + 1) + random.random())
    raise last  # pragma: no cover


def _header(text: str, limit: int = 200) -> str:
    """En-têtes HTTP : une ligne, latin-1 uniquement (pas d'emoji)."""
    return " ".join(str(text).split()).encode("latin-1", "replace").decode("latin-1")[:limit]


def retailer_actions(url: str):
    """Boutons 1-tap + rappel, UNIQUEMENT pour les grandes enseignes.
    Retourne (actions, rappel). Le bot n'ajoute rien au panier lui-même : le panier
    appartient à TON compte, dans TON navigateur."""
    host = urlparse(url).netloc.lower()
    if not any(k in host for k in BIG_RETAILERS):
        return None, ""
    actions = [("Ouvrir la page", url)]
    if "amazon." in host:
        m = AMAZON_ASIN_RE.search(url)
        if m:  # lien d'ajout au panier officiel d'Amazon : ouvre TON panier, 1 clic pour valider
            actions.append(("Ajouter au panier",
                            f"https://{host}/gp/aws/cart/add.html?ASIN.1={m.group(1)}&Quantity.1=1"))
    tip = "\nGrande enseigne : sois déjà connecté, ouvre la page et ajoute au panier tout de suite."
    return actions, tip


def notify(title: str, message: str, url: str = "", priority: str = "5",
           tags: str = "rotating_light", actions=None) -> bool:
    """Envoie une notif ntfy (3 essais). Retourne True seulement si elle est partie."""
    if TOPIC_UNSET:
        print("  ! NTFY_TOPIC n'est pas configuré : notification non envoyée.")
        return False
    endpoint = "https://ntfy.sh/" + urllib.parse.quote(NTFY_TOPIC, safe="")
    headers = {"Title": _header(title), "Priority": str(priority), "Tags": tags}
    if url:
        headers["Click"] = urllib.parse.quote(url, safe=":/?&=%#@+,;~!$*()[]")
    if actions:  # boutons ntfy ; on saute les URL contenant , ou ; (syntaxe ntfy)
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
        except Exception as e:  # noqa: BLE001
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
    """Lit products.txt : 'Nom | URL', # = commentaire. Retourne [(nom, url), ...]."""
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
    except Exception as e:  # noqa: BLE001
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
    """Écriture atomique, et seulement si le contenu a changé."""
    try:
        text = json.dumps(state, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        try:
            if STATE_FILE.read_text(encoding="utf-8") == text:
                return
        except OSError:
            pass
        tmp = STATE_FILE.with_name(STATE_FILE.name + ".tmp")
        tmp.write_text(text, encoding="utf-8")
        os.replace(tmp, STATE_FILE)
    except Exception as e:  # noqa: BLE001
        print(f"! impossible d'écrire l'état : {e}")


def alert_limited(state: dict, key: str, title: str, message: str) -> None:
    """Alerte 'technique' au plus une fois toutes les ALERT_COOLDOWN_HOURS."""
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
    except Exception as e:  # noqa: BLE001
        res["error"] = f"erreur inattendue ({e.__class__.__name__}: {str(e)[:60]})"
    return res


def check_group(items: list, deadline: float) -> list:
    """Vérifie les pages d'un même site, l'une après l'autre, avec pause."""
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
            except Exception as e:  # noqa: BLE001
                for name, url in group:
                    results[url] = {"name": name, "url": url, "status": None, "source": None,
                                    "error": f"erreur interne ({e.__class__.__name__})",
                                    "skipped": False}
    return results


def run_once(state: dict, products: list) -> None:
    started = time.monotonic()
    print(f"\n[{datetime.now():%H:%M:%S}] Vérification de {len(products)} produit(s)...")
    results = fetch_all(products, started + RUN_DEADLINE)

    entries = state["products"]
    current = {url for _, url in products}
    for url in [u for u in entries if u not in current]:
        del entries[url]  # produit retiré de products.txt

    ok = available = failing = skipped = 0
    problems, recovered = [], []

    for name, url in products:
        res = results[url]
        entry = entries.setdefault(url, new_entry())

        if res["skipped"]:
            skipped += 1
            print(f"- {name}: ignoré (temps du tour dépassé)")
            continue

        status, source, err = res["status"], res["source"], res["error"]
        if not err and status == "unknown":
            err = "page illisible (structure du site changée ?)"
        if not err and status == "blocked":
            err = "page de vérification / protection anti-bot"

        if err:
            failing += 1
            now = time.time()
            if not entry["problem_since"]:
                entry["problem_since"] = now
            minutes = (now - entry["problem_since"]) / 60
            print(f"- {name}: {err} [depuis {minutes:.0f} min]")
            if minutes >= PROBLEM_ALERT_MINUTES and not entry["problem_alerted"]:
                problems.append((name, err, entry))
            continue

        # Lecture réussie
        if entry["problem_alerted"]:
            recovered.append(name)
        entry["problem_since"] = 0
        entry["problem_alerted"] = False
        entry["status"] = status
        ok += 1
        label = {"in": "EN STOCK", "preorder": "PRÉCOMMANDE", "out": "épuisé"}[status]
        print(f"- {name}: {label}" + (" (mots-clés)" if source == "keywords" else ""))

        is_available = status == "in" or (status == "preorder" and ALERT_ON_PREORDER)
        if not is_available:
            entry["alerted"] = False   # ré-armé pour le prochain restock
            entry["weak_hits"] = 0
            continue

        available += 1
        if entry["alerted"]:
            continue
        if source == "keywords":
            entry["weak_hits"] += 1
            if entry["weak_hits"] < WEAK_CONFIRMATIONS:
                print("  ... détection peu fiable : à confirmer au prochain tour")
                continue

        kind = "Stock dispo" if status == "in" else "Précommande ouverte"
        note = "\n(détection par mots-clés : vérifie la page)" if source == "keywords" else ""
        # "alerted" n'est validé que si la notif est bien partie -> sinon réessai
        actions, tip = retailer_actions(url)
        if notify(f"{kind} : {name}", f"{name}\n{url}{note}{tip}", url, actions=actions):
            entry["alerted"] = True

    if problems:
        lines = "\n".join(f"- {n} : {why}" for n, why, _ in problems)
        if notify("Bot Pokémon : site en difficulté",
                  f"Ces pages ne sont plus lues correctement :\n{lines}\n"
                  "Tu risques de rater du stock dessus : vérifie à la main.",
                  priority="4", tags="warning"):
            for _, _, entry in problems:
                entry["problem_alerted"] = True

    if recovered:
        notify("Bot Pokémon : sites de nouveau lisibles",
               "\n".join(f"- {n}" for n in recovered), priority="2", tags="white_check_mark")

    if HEARTBEAT_EVERY_HOURS > 0 and \
            time.time() - state.get("last_heartbeat", 0) >= HEARTBEAT_EVERY_HOURS * 3600:
        msg = (f"Le bot tourne. {ok}/{len(products)} pages lues correctement, "
               f"{available} disponible(s), {failing} en difficulté.")
        if notify("Bot Pokémon : OK", msg, priority="2", tags="white_check_mark"):
            state["last_heartbeat"] = time.time()

    save_state(state)
    print(f"Terminé en {time.monotonic() - started:.0f}s : {ok} OK, {failing} en difficulté, "
          f"{available} disponible(s)" + (f", {skipped} ignoré(s)" if skipped else "") + ".")


def safe_cycle(state: dict) -> None:
    """Un tour complet qui ne plante jamais : tout problème devient une alerte ntfy."""
    try:
        products = load_products()
    except ConfigError as e:
        print(f"! {e}")
        alert_limited(state, "last_config_alert", "Bot Pokémon : products.txt invalide", str(e))
        save_state(state)
        return
    try:
        run_once(state, products)
    except Exception:  # noqa: BLE001
        trace = traceback.format_exc()
        print(trace)
        last_line = trace.strip().splitlines()[-1][:300]
        alert_limited(state, "last_crash_alert", "Bot Pokémon : erreur interne", last_line)
        save_state(state)


def fast_loop(state: dict, duration: int, interval: int) -> None:
    """Mode rapide : plusieurs vérifications dans un même tour GitHub Actions."""
    interval = max(MIN_INTERVAL, interval)
    started = time.monotonic()
    end = started + duration
    cycles = 0
    while True:
        cycle_start = time.monotonic()
        safe_cycle(state)
        cycles += 1
        wait = max(5.0, interval + random.uniform(-4, 4) - (time.monotonic() - cycle_start))
        if time.monotonic() + wait >= end:  # pas le temps d'un autre passage complet
            break
        time.sleep(wait)
    print(f"\nMode rapide terminé : {cycles} vérification(s) en "
          f"{time.monotonic() - started:.0f}s (toutes les ~{interval}s).")


def main() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:  # noqa: BLE001
            pass

    parser = argparse.ArgumentParser(description="Surveillance de stock Pokémon / One Piece")
    parser.add_argument("--once", action="store_true", help="un seul tour puis quitte")
    parser.add_argument("--fast", action="store_true",
                        help="mode rapide : vérifie toutes les ~30 s pendant ~4,5 min")
    parser.add_argument("--duration", type=int, default=FAST_DURATION,
                        help="durée du mode rapide en secondes")
    parser.add_argument("--interval", type=int, default=FAST_INTERVAL,
                        help="secondes entre deux vérifications du mode rapide")
    parser.add_argument("--test", action="store_true", help="envoie une notification de test")
    args = parser.parse_args()

    if args.test:
        ok = notify("Test bot Pokemon", "Si tu vois ce message, les notifications marchent.",
                    priority="3", tags="white_check_mark")
        sys.exit(0 if ok else 1)

    state = load_state()
    if args.once:
        safe_cycle(state)
        return
    if args.fast:
        fast_loop(state, args.duration, args.interval)
        return

    print("Bot lancé. Ctrl+C pour arrêter.")
    try:
        while True:
            safe_cycle(state)
            time.sleep(CHECK_EVERY + random.uniform(0, 30))
    except KeyboardInterrupt:
        print("\nArrêt.")


if __name__ == "__main__":
    main()
