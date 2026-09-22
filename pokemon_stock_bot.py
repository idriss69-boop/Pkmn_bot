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
  python3 pokemon_stock_bot.py --test    envoie une notification de test (tous canaux)

MODE RAPIDE sur GitHub : Settings > Secrets and variables > Actions > onglet Variables >
New repository variable : nom FAST_MODE, valeur on. Supprime-la (ou mets off) pour
revenir au mode normal. Réserve-le aux jours de sortie.

NOTIFICATIONS MULTI-CANAL : en plus du secret NTFY_TOPIC, tu peux ajouter deux secrets
GitHub optionnels pour recevoir les alertes aussi sur Telegram (utile si ntfy.sh a un
coup de mou pile le jour où ça compte) :
  TELEGRAM_BOT_TOKEN   token du bot (via @BotFather)
  TELEGRAM_CHAT_ID     ID de ton chat (via @userinfobot par exemple)
Si ces deux secrets ne sont pas définis, le bot continue de fonctionner avec ntfy
seul, comme avant.

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

# Canal Telegram (optionnel, en plus de ntfy) : les deux secrets doivent être définis
# pour que Telegram soit utilisé. Sinon le bot continue avec ntfy seul.
TELEGRAM_BOT_TOKEN = (os.environ.get("TELEGRAM_BOT_TOKEN") or "").strip()
TELEGRAM_CHAT_ID = (os.environ.get("TELEGRAM_CHAT_ID") or "").strip()

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


def _notify_ntfy(title: str, message: str, url: str = "", priority: str = "5",
                  tags: str = "rotating_light", actions=None) -> bool:
    """Envoie une notif ntfy (3 essais). Retourne True seulement si elle est partie."""
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
            print("  -> notification ntfy envoyée")
            return True
        except Exception as e:  # noqa: BLE001
            error = e
            if attempt < 2:
                time.sleep(2 * (attempt + 1))
    print(f"  ! échec de la notification ntfy, nouvel essai au prochain tour : {error}")
    return False


def _notify_telegram(title: str, message: str, url: str = "", actions=None) -> bool:
    """Envoie une notif Telegram (3 essais) avec boutons liens si fournis.
    Ne fait qu'ouvrir des liens : aucune action n'est déclenchée côté site marchand."""
    endpoint = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    text = f"{title}\n\n{message}"[:4000]
    buttons = [[{"text": label, "url": u}] for label, u in (actions or [])
               if u.startswith(("http://", "https://"))]
    if not buttons and url:
        buttons = [[{"text": "Ouvrir la page", "url": url}]]
    payload = {"chat_id": TELEGRAM_CHAT_ID, "text": text, "disable_web_page_preview": False}
    if buttons:
        payload["reply_markup"] = {"inline_keyboard": buttons}
    data = json.dumps(payload).encode("utf-8")

    error = None
    for attempt in range(3):
        try:
            req = urllib.request.Request(endpoint, data=data,
                                         headers={"Content-Type": "application/json"}, method="POST")
            with urllib.request.urlopen(req, timeout=15) as r:
                resp = json.loads(r.read().decode("utf-8"))
            if resp.get("ok"):
                print("  -> notification Telegram envoyée")
                return True
            error = resp.get("description", "réponse Telegram invalide")
        except Exception as e:  # noqa: BLE001
            error = e
        if attempt < 2:
            time.sleep(2 * (attempt + 1))
    print(f"  ! échec de la notification Telegram, nouvel essai au prochain tour : {error}")
    return False


def notify(title: str, message: str, url: str = "", priority: str = "5",
           tags: str = "rotating_light", actions=None) -> bool:
    """Envoie la notif sur tous les canaux configurés (ntfy + Telegram si les deux
    secrets sont réglés). Un canal en panne ne bloque pas l'autre.
    Retourne True si AU MOINS UN canal est parti (pour marquer l'alerte comme envoyée)."""
    channels = []
    if TOPIC_UNSET:
        print("  ! NTFY_TOPIC n'est pas configuré : ntfy sauté.")
    else:
        channels.append(("ntfy", lambda: _notify_ntfy(title, message, url, priority, tags, actions)))
    if TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
        channels.append(("telegram", lambda: _notify_telegram(title, message, url, actions)))

    if not channels:
        print("  ! Aucun canal de notification configuré (ni NTFY_TOPIC, ni Telegram).")
        return False

    results = {}
    with ThreadPoolExecutor(max_workers=len(channels)) as ex:
        futures = {ex.submit(fn): name for name, fn in channels}
        for fut, name in futures.items():
            try:
                results[name] = fut.result()
            except Exception as e:  # noqa: BLE001
                print(f"  ! canal {name} : erreur interne ({e.__class__.__name__})")
                results[name] = False
    return any(results.values())


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
        return stat
