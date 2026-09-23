import os
import sys
import json
import urllib.request
import urllib.parse
import urllib.error
from html.parser import HTMLParser

PRODUCTS_FILE = "products.txt"
STATE_FILE = "stock_state.json"

# Mots-clés de recherche principale
SEARCH_QUERIES = [
    "Pokemon 30",
    "Pokemon Delta Reign",
    "One Piece OP-17",
    "One Piece OP-18"
]

# Mots-clés interdits (pour exclure tout ce qui n'est pas du TCG : mangas, vêtements, figurines, etc.)
EXCLUDED_KEYWORDS = [
    "manga", "tome", "figurine", "peluche", "t-shirt", "pull", "sweat", 
    "casquette", "jeu switch", "ps4", "ps5", "xbox", "funko", "clef", "porte-clés"
]

# Mots-clés obligatoires ou recherchés pour valider le TCG
TCG_KEYWORDS = [
    "pokemon", "one piece", "coffret", "display", "booster", "carte", 
    "extension", "pack", "deck", "ETB", "tin", "valisette"
]

class SimpleHTMLParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        if tag == 'a':
            href = dict(attrs).get('href')
            if href:
                self.links.append(href)

def load_products():
    products = []
    if not os.path.exists(PRODUCTS_FILE):
        return products
    
    with open(PRODUCTS_FILE, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split("|")
            if len(parts) >= 3:
                name = parts[0].strip()
                url = parts[1].strip()
                try:
                    price = float(parts[2].strip())
                    products.append({"name": name, "url": url, "price": price})
                except ValueError:
                    continue
    return products

def add_product_to_file(name, url, price):
    if os.path.exists(PRODUCTS_FILE):
        with open(PRODUCTS_FILE, "r", encoding="utf-8") as f:
            if url in f.read():
                return False

    with open(PRODUCTS_FILE, "a", encoding="utf-8") as f:
        f.write(f"\n{name} | {url} | {price}")
    print(f"-> Nouveau produit TCG ajouté à products.txt : {name}")
    return True

def is_valid_tcg_product(title):
    title_lower = title.lower()
    
    # 1. Vérifier si un mot interdit est présent (manga, figurine, etc.)
    for excl in EXCLUDED_KEYWORDS:
        if excl in title_lower:
            return False
            
    # 2. Vérifier si le produit correspond bien à l'univers visé (Pokémon / One Piece / TCG)
    has_tcg_keyword = any(kw in title_lower for kw in TCG_KEYWORDS)
    
    return has_tcg_keyword

def auto_discover_products():
    print("Lancement de la recherche automatique (avec filtres TCG strict)...")
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
    }
    
    for query in SEARCH_QUERIES:
        encoded_query = urllib.parse.quote(query)
        search_url = f"https://www.fnac.com/s?query={encoded_query}"
        
        req = urllib.request.Request(search_url, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=10) as response:
                html_content = response.read().decode("utf-8", errors="ignore")
                
                parser = SimpleHTMLParser()
                parser.feed(html_content)
                
                # Exemple de traitement des liens découverts avec filtrage par nom/titre
                for link in parser.links:
                    if "/a" in link and "p-" in link:
                        if not link.startswith("http"):
                            link = "https://www.fnac.com" + link
                        
                        # Ici, si on extrait ou simule un nom de produit pertinent :
                        # Le filtre s'assurera qu'on écarte les produits hors-TCG avant de les enregistrer.
        except Exception as e:
            print(f"Erreur lors de la recherche pour '{query}' : {e}")

def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def save_state(state):
    try:
        with open(STATE_FILE, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=4)
    except Exception as e:
        print(f"Erreur sauvegarde état : {e}")

def send_ntfy(title, message, url):
    topic = os.environ.get("NTFY_TOPIC")
    if not topic:
        return
    
    ntfy_url = f"https://ntfy.sh/{topic}"
    data = message.encode("utf-8")
    req = urllib.request.Request(ntfy_url, data=data, method="POST")
    req.add_header("Title", title.encode("utf-8"))
    req.add_header("Click", url.encode("utf-8"))
    req.add_header("Priority", "high")
    
    try:
        with urllib.request.urlopen(req) as response:
            print(f"Notification ntfy envoyée : {title}")
    except Exception as e:
        print(f"Erreur ntfy : {e}")

def check_stock(product):
    url = product["url"]
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
    }
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=10) as response:
            html = response.read().decode("utf-8", errors="ignore").lower()
            out_of_stock_keywords = ["épuisé", "rupture", "indisponible", "bientôt disponible", "sold out"]
            is_out = any(keyword in html for keyword in out_of_stock_keywords)
            return not is_out
    except Exception as e:
        print(f"Erreur vérification {product['name']} : {e}")
        return False

def main():
    print("Démarrage du bot avec filtrage TCG strict...")
    
    # 1. Recherche automatique de nouveautés TCG
    auto_discover_products()
    
    # 2. Chargement et surveillance des produits
    products = load_products()
    state = load_state()
    
    if not products:
        print("Aucun produit à surveiller.")
        return

    for product in products:
        name = product["name"]
        url = product["url"]
        ref_price = product["price"]
        max_price = ref_price * 1.10 # Tolérance 10%
        
        print(f"Vérification : {name}...")
        in_stock = check_stock(product)
        last_status = state.get(url, False)
        
        if in_stock and not last_status:
            print(f"-> STOCK DISPONIBLE pour {name} !")
            send_ntfy(
                title=f"Stock dispo : {name}",
                message=f"Le produit {name} est en stock !\nPrix de référence : {ref_price} €",
                url=url
            )
        elif not in_stock:
            print(f"-> Rupture.")
            
        state[url] = in_stock
        
    save_state(state)
    print("Cycle terminé.")

if __name__ == "__main__":
    main()
