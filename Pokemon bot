#!/usr/bin/env python3
"""
Bot de surveillance de stock Pokémon + One Piece TCG - VERSION FINALE

- Aucune dépendance : Python 3.8+ suffit.
- Te prévient par notification push via ntfy.sh (gratuit, sans compte).
- Il ne fait que DÉTECTER le stock : il n'achète rien à ta place.

FIABILITÉ
1. Réessai : une alerte de stock n'est marquée "envoyée" que si la notif est
   bien partie. Sinon, le bot retente au tour suivant.
2. Message de survie : toutes les HEARTBEAT_EVERY_HOURS heures, une notif discrète
   "le bot tourne". Si elle n'arrive plus, c'est que le bot est tombé.
3. Alerte de problème : si un site est bloqué / en erreur / illisible pendant
   PROBLEM_ALERT_AFTER tours de suite, tu es prévenu.

MISE EN ROUTE
1. Installe l'app "ntfy" (iOS / Android) et abonne-toi à un nom secret unique,
   par exemple : pokestock-idriss-8472
2. Mets ce nom dans NTFY_TOPIC (ou variable d'environnement NTFY_TOPIC).
3. Test :     python3 pokemon_stock_bot.py --test
4. Lancement: python3 pokemon_stock_bot.py          (boucle continue)
              python3 pokemon_stock_bot.py --once   (un seul tour : GitHub Actions / cron)

TERMUX (Android) : pkg install python, puis termux-wake-lock, puis lance le script.
Désactive l'économie de batterie pour Termux et laisse le téléphone branché.

Pour ajouter un produit : ajoute une ligne dans products.txt  ->  Nom | URL de la fiche produit.
(Colle l'URL de la page du PRODUIT lui-même, pas d'une page de recherche ou de catégorie.)
"""

import argparse
import gzip
import json
import os
import random
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime
from pathlib import Path

# ----------------------------------------------------------------------------
# CONFIG
# ----------------------------------------------------------------------------

NTFY_TOPIC = os.environ.get("NTFY_TOPIC", "CHANGE-MOI-pokestock-secret-123")

CHECK_EVERY = 180            # secondes entre deux tours en mode boucle
ALERT_ON_PREORDER = True     # alerter aussi quand la précommande s'ouvre
HEARTBEAT_EVERY_HOURS = 24   # message "je tourne" (0 pour désactiver)
PROBLEM_ALERT_AFTER = 6      # tours de suite en échec avant d'alerter (6 x 5 min = 30 min)

PRODUCTS_FILE = Path(__file__).with_name("products.txt")


def load_products() -> dict:
    """Lit products.txt : une ligne = 'Nom affiché | URL'. Les lignes # sont ignorées."""
    products = {}
    try:
        lines = PRODUCTS_FILE.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        sys.exit(f"Fichier introuvable : {PRODUCTS_FILE}\n"
                 "Crée products.txt à côté du script (une ligne = 'Nom | URL').")
    for n, line in enumerate(lines, 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "|" not in line:
            print(f"! products.txt ligne {n} ignorée (format attendu : Nom | URL)")
            continue
        name, url = (part.strip() for part in line.split("|", 1))
        if not url.startswith("http") or "..." in url:
            print(f"! products.txt ligne {n} ignorée (URL invalide) : {name}")
            continue
        products[name] = url
    if not products:
        sys.exit("products.txt ne contient aucun produit valide.")
    return products


PRODUCTS = load_products()

STATE_FILE = Path(__file__).with_name("stock_state.json")

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

# ----------------------------------------------------------------------------
# DÉTECTION
# ----------------------------------------------------------------------------

# 1) Données structurées (schema.org) : la méthode la plus fiable
SCHEMA_RE = re.compile(
    r'(?:schema\.org/|"availability"\s*:\s*")'
    r"(InStock|LimitedAvailability|OnlineOnly|InStoreOnly|"
    r"PreOrder|PreSale|BackOrder|"
    r"OutOfStock|SoldOut|Discontinued)",
    re.I,
)
# 2) Balise Open Graph : <meta property="product:availability" content="in stock">
OG_RE = re.compile(r'product:availability["\']\s+content=["\']([^"\']+)["\']', re.I)

IN_KEYS = {"instock", "limitedavailability", "onlineonly", "instoreonly", "in stock"}
PRE_KEYS = {"preorder", "presale", "backorder"}
OUT_KEYS = {"outofstock", "soldout", "discontinued", "out of stock", "oos"}

# 3) Repli par mots-clés (moins fiable)
OUT_WORDS = [
    "épuisé", "epuise", "rupture de stock", "out of stock", "sold out",
    "indisponible", "actuellement indisponible", "plus disponible", "victime de son succès",
]
IN_WORDS = ["ajouter au panier", "add to cart", "ajouter à la commande", "acheter maintenant"]
PRE_WORDS = ["précommande", "precommande", "pre-order", "preorder"]


def classify(html: str) -> str:
    """Retourne 'in', 'preorder', 'out' ou 'unknown'."""
    found = {m.lower() for m in SCHEMA_RE.findall(html)}
    found |= {m.strip().lower() for m in OG_RE.findall(html)}

    if found & IN_KEYS:
        return "in"
    if found & PRE_KEYS:
        return "preorder"
    if found & OUT_KEYS:
        return "out"

    low = html.lower()
    if any(w in low for w in OUT_WORDS):
        return "out"
    if any(w in low for w in PRE_WORDS) and any(w in low for w in IN_WORDS):
        return "preorder"
    if any(w in low for w in IN_WORDS):
        return "in"
    return "unknown"


def fetch(url: str) -> str:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml",
            "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.5",
            "Accept-Encoding": "gzip",
        },
    )
    with urllib.request.urlopen(req, timeout=20) as r:
        raw = r.read()
        if r.headers.get("Content-Encoding", "").lower() == "gzip":
            raw = gzip.decompress(raw)
        charset = r.headers.get_content_charset() or "utf-8"
        return raw.decode(charset, errors="replace")


# ----------------------------------------------------------------------------
# NOTIFICATIONS
# ----------------------------------------------------------------------------

def notify(title: str, message: str, url: str = "", priority: str = "5",
           tags: str = "rotating_light") -> bool:
    """Envoie une notif ntfy. Retourne True seulement si elle est bien partie."""
    if NTFY_TOPIC.startswith("CHANGE-MOI"):
        print("  ! NTFY_TOPIC n'est pas configuré : notification non envoyée.")
        return False
    headers = {
        # Les en-têtes HTTP doivent rester en latin-1 (pas d'emoji ici)
        "Title": title.encode("latin-1", "replace").decode("latin-1"),
        "Priority": priority,
        "Tags": tags,
    }
    if url:
        headers["Click"] = url
    req = urllib.request.Request(
        f"https://ntfy.sh/{NTFY_TOPIC}",
        data=message.encode("utf-8"),
        headers=headers,
        method="POST",
    )
    try:
        urllib.request.urlopen(req, timeout=15).read()
        print("  -> notification envoyée")
        return True
    except Exception as e:  # noqa: BLE001
        print(f"  ! échec de la notification (nouvel essai au prochain tour) : {e}")
        return False


# ----------------------------------------------------------------------------
# ÉTAT
# ----------------------------------------------------------------------------

def new_entry() -> dict:
    return {"status": None, "alerted": False, "problems": 0, "problem_alerted": False}


def load_state() -> dict:
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        if isinstance(data, dict) and "products" in data:
            return data
    except Exception:  # noqa: BLE001
        pass
    return {"products": {}, "last_heartbeat": 0}


def save_state(state: dict) -> None:
    try:
        STATE_FILE.write_text(json.dumps(state, indent=2, ensure_ascii=False), encoding="utf-8")
    except Exception as e:  # noqa: BLE001
        print(f"  ! impossible d'écrire l'état : {e}")


# ----------------------------------------------------------------------------
# TOUR DE VÉRIFICATION
# ----------------------------------------------------------------------------

def run_once(state: dict) -> None:
    print(f"\n[{datetime.now().strftime('%H:%M:%S')}] Vérification de {len(PRODUCTS)} produit(s)...")
    products = state["products"]
    problems = []          # (name, url, raison, entry) à signaler
    ok_count = 0
    available_count = 0

    for name, url in PRODUCTS.items():
        entry = products.setdefault(url, new_entry())
        status, err = None, None

        try:
            status = classify(fetch(url))
        except urllib.error.HTTPError as e:
            err = f"erreur HTTP {e.code} (site qui bloque les bots ?)"
        except Exception as e:  # noqa: BLE001
            err = f"erreur ({str(e)[:80]})"

        if status == "unknown":
            err, status = "page illisible (structure du site changée ?)", None

        if err:
            entry["problems"] += 1
            print(f"- {name}: {err} [{entry['problems']} tour(s) de suite]")
            if entry["problems"] >= PROBLEM_ALERT_AFTER and not entry["problem_alerted"]:
                problems.append((name, url, err, entry))
            time.sleep(random.uniform(2, 5))
            continue

        # Lecture réussie
        entry["problems"] = 0
        entry["problem_alerted"] = False
        entry["status"] = status
        ok_count += 1
        label = {"in": "EN STOCK", "preorder": "PRÉCOMMANDE", "out": "épuisé"}[status]
        print(f"- {name}: {label}")

        available = status == "in" or (status == "preorder" and ALERT_ON_PREORDER)
        if available:
            available_count += 1
            # On n'est "alerté" qu'une fois la notif bien partie -> sinon réessai au prochain tour
            if not entry["alerted"]:
                kind = "Stock dispo" if status == "in" else "Précommande ouverte"
                if notify(f"{kind} : {name}", f"{name}\n{url}", url):
                    entry["alerted"] = True
        else:
            entry["alerted"] = False  # re-armé pour le prochain restock

        time.sleep(random.uniform(2, 5))

    # Alerte de problème (une seule notif regroupée)
    if problems:
        lines = "\n".join(f"- {n} : {why}" for n, _, why, _ in problems)
        if notify("Bot Pokémon : site en difficulté",
                  f"Ces pages ne sont plus lues correctement :\n{lines}\n"
                  "Tu risques de rater du stock dessus : vérifie à la main.",
                  priority="4", tags="warning"):
            for _, _, _, entry in problems:
                entry["problem_alerted"] = True

    # Message de survie
    if HEARTBEAT_EVERY_HOURS > 0:
        if time.time() - state.get("last_heartbeat", 0) >= HEARTBEAT_EVERY_HOURS * 3600:
            msg = (f"Le bot tourne. {ok_count}/{len(PRODUCTS)} pages lues correctement, "
                   f"{available_count} disponible(s).")
            if notify("Bot Pokémon : OK", msg, priority="2", tags="white_check_mark"):
                state["last_heartbeat"] = time.time()

    save_state(state)


def main() -> None:
    parser = argparse.ArgumentParser(description="Surveillance de stock Pokémon")
    parser.add_argument("--once", action="store_true", help="un seul tour puis quitte")
    parser.add_argument("--test", action="store_true", help="envoie une notification de test")
    args = parser.parse_args()

    if args.test:
        ok = notify("Test bot Pokémon", "Si tu vois ce message, les notifications marchent.",
                    priority="3", tags="white_check_mark")
        sys.exit(0 if ok else 1)

    state = load_state()
    if args.once:
        run_once(state)
        return

    print("Bot lancé. Ctrl+C pour arrêter.")
    try:
        while True:
            run_once(state)
            time.sleep(CHECK_EVERY + random.uniform(0, 30))
    except KeyboardInterrupt:
        print("\nArrêt.")
        sys.exit(0)


if __name__ == "__main__":
    main()
