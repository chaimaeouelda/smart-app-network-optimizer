import tkinter as tk
from tkinter import ttk, messagebox
import random
import heapq
from collections import deque
import copy

# --------- Fonctions de génération de graphes ---------
def generate_directed_graph(nodes, max_weight=20):
    graph = {node: {} for node in nodes}
    for node in nodes:
        possible_neighbors = [n for n in nodes if n != node]
        nb_neighbors = random.randint(2, min(5, len(possible_neighbors)))
        neighbors = random.sample(possible_neighbors, nb_neighbors)
        for nbr in neighbors:
            weight = random.randint(1, max_weight)
            graph[node][nbr] = weight
    return graph

def generate_undirected_graph(nodes, max_weight=20):
    graph = {node: {} for node in nodes}
    for node in nodes:
        possible_neighbors = [n for n in nodes if n != node]
        nb_neighbors = random.randint(2, min(5, len(possible_neighbors)))
        neighbors = random.sample(possible_neighbors, nb_neighbors)
        for nbr in neighbors:
            weight = random.randint(1, max_weight)
            graph[node][nbr] = weight
            graph[nbr][node] = weight
    return graph

# --------- Algorithmes ---------
def dijkstra(graph, start):
    distances = {node: float('inf') for node in graph}
    distances[start] = 0
    pq = [(0, start)]
    while pq:
        dist, node = heapq.heappop(pq)
        if dist > distances[node]:
            continue
        for neighbor, weight in graph[node].items():
            new_dist = dist + weight
            if new_dist < distances[neighbor]:
                distances[neighbor] = new_dist
                heapq.heappush(pq, (new_dist, neighbor))
    return distances

def bellman_ford(graph, start):
    distances = {node: float('inf') for node in graph}
    distances[start] = 0
    for _ in range(len(graph) - 1):
        for u in graph:
            for v, w in graph[u].items():
                if distances[u] + w < distances[v]:
                    distances[v] = distances[u] + w
    for u in graph:
        for v, w in graph[u].items():
            if distances[u] + w < distances[v]:
                raise ValueError("Cycle négatif détecté")
    return distances

class UnionFind:
    def __init__(self, nodes):
        self.parent = {node: node for node in nodes}
        self.rank = {node: 0 for node in nodes}
    def find(self, u):
        if self.parent[u] != u:
            self.parent[u] = self.find(self.parent[u])
        return self.parent[u]
    def union(self, u, v):
        root_u = self.find(u)
        root_v = self.find(v)
        if root_u == root_v:
            return False
        if self.rank[root_u] < self.rank[root_v]:
            self.parent[root_u] = root_v
        else:
            self.parent[root_v] = root_u
            if self.rank[root_u] == self.rank[root_v]:
                self.rank[root_u] += 1
        return True

def kruskal(graph):
    edges = []
    for u in graph:
        for v, w in graph[u].items():
            if u < v:
                edges.append((w, u, v))
    edges.sort()
    uf = UnionFind(graph.keys())
    mst = []
    total_weight = 0
    for w, u, v in edges:
        if uf.union(u, v):
            mst.append((u, v, w))
            total_weight += w
    return mst, total_weight

def welsh_powell(graph):
    degree_sorted = sorted(graph, key=lambda x: len(graph[x]), reverse=True)
    color = {}
    current_color = 0
    for node in degree_sorted:
        if node not in color:
            current_color += 1
            color[node] = current_color
            for other in degree_sorted:
                if other not in color and all(color.get(neigh) != current_color for neigh in graph[other]):
                    color[other] = current_color
    return color

def ford_fulkerson(graph, source, sink):
    residual = {u: {} for u in graph}
    for u in graph:
        for v, cap in graph[u].items():
            residual[u][v] = cap
            residual.setdefault(v, {}).setdefault(u, 0)
    max_flow = 0

    def bfs():
        queue = deque([source])
        paths = {source: []}
        while queue:
            u = queue.popleft()
            for v in residual[u]:
                if residual[u][v] > 0 and v not in paths:
                    paths[v] = paths[u] + [(u, v)]
                    if v == sink:
                        return paths[v]
                    queue.append(v)
        return None

    path = bfs()
    while path:
        flow = min(residual[u][v] for u, v in path)
        for u, v in path:
            residual[u][v] -= flow
            residual[v][u] += flow
        max_flow += flow
        path = bfs()
    return max_flow, residual

def potentiel_metra(graph):
    earliest = {node: 0 for node in graph}
    visited = set()

    # Dates au plus tôt
    for node in graph:
        for neighbor, duration in graph[node].items():
            earliest[neighbor] = max(earliest.get(neighbor, 0), earliest[node] + duration)

    # Temps total du projet
    max_time = max(earliest.values(), default=0)

    latest = {node: max_time for node in graph}
    # Dates au plus tard
    for node in reversed(list(graph.keys())):
        for neighbor, duration in graph[node].items():
            latest[node] = min(latest[node], latest[neighbor] - duration)

    marge = {node: latest[node] - earliest[node] for node in graph}
    return earliest, latest, marge

# --------- Méthodes pour problèmes de transport ---------
def north_west_corner_method(supply, demand):
    i, j = 0, 0
    supply = supply.copy()
    demand = demand.copy()
    allocation = [[0] * len(demand) for _ in range(len(supply))]
    
    while i < len(supply) and j < len(demand):
        allocated = min(supply[i], demand[j])
        allocation[i][j] = allocated
        supply[i] -= allocated
        demand[j] -= allocated
        
        if supply[i] == 0:
            i += 1
        if demand[j] == 0:
            j += 1
    
    return allocation

def moindre_cout_method(supply, demand, cost_matrix):
    supply = supply.copy()
    demand = demand.copy()
    allocation = [[0] * len(demand) for _ in range(len(supply))]
    
    while True:
        min_cost = float('inf')
        min_i, min_j = -1, -1
        
        for i in range(len(supply)):
            if supply[i] == 0:
                continue
            for j in range(len(demand)):
                if demand[j] == 0:
                    continue
                if cost_matrix[i][j] < min_cost:
                    min_cost = cost_matrix[i][j]
                    min_i, min_j = i, j
        
        if min_i == -1 or min_j == -1:
            break
        
        allocated = min(supply[min_i], demand[min_j])
        allocation[min_i][min_j] = allocated
        supply[min_i] -= allocated
        demand[min_j] -= allocated
    
    return allocation

def calculate_transport_cost(allocation, cost_matrix):
    total_cost = 0
    for i in range(len(allocation)):
        for j in range(len(allocation[i])):
            total_cost += allocation[i][j] * cost_matrix[i][j]
    return total_cost

def generate_transport_problem(num_sources=4, num_destinations=4):
    # Génération aléatoire des capacités d'offre et des demandes
    supply = [random.randint(15, 40) for _ in range(num_sources)]
    demand = [random.randint(15, 40) for _ in range(num_destinations)]
    
    # Équilibrer le problème
    total_supply = sum(supply)
    total_demand = sum(demand)
    
    if total_supply > total_demand:
        demand.append(total_supply - total_demand)
        num_destinations += 1
    elif total_demand > total_supply:
        supply.append(total_demand - total_supply)
        num_sources += 1
    
    # Génération de la matrice de coûts
    cost_matrix = []
    for i in range(num_sources):
        row = []
        for j in range(num_destinations):
            if i == num_sources - 1 and num_sources > 4:  # Source fictive
                row.append(0)
            elif j == num_destinations - 1 and num_destinations > 4:  # Destination fictive
                row.append(0)
            else:
                row.append(random.randint(5, 25))
        cost_matrix.append(row)
    
    return supply, demand, cost_matrix

# --------- Algorithme Stepping Stone ---------
def stepping_stone_method(supply, demand, cost_matrix, initial_allocation):
    # Copie des structures de données pour éviter de modifier les originaux
    supply = supply.copy()
    demand = demand.copy()
    allocation = copy.deepcopy(initial_allocation)
    num_sources = len(supply)
    num_destinations = len(demand)
    
    def find_cycle(i, j, visited=None, path=None):
        if visited is None:
            visited = set()
        if path is None:
            path = []
        
        # Vérifier si nous sommes revenus à la case de départ
        if len(path) >= 4 and path[0] == (i, j):
            return path
        
        # Marquer la case actuelle comme visitée
        visited.add((i, j))
        path.append((i, j))
        
        # Rechercher dans les lignes et colonnes pour trouver une case allouée
        # qui n'a pas encore été visitée et qui complète le cycle
        for k in range(num_sources):
            if k != i and allocation[k][j] > 0 and (k, j) not in visited:
                result = find_cycle(k, j, visited.copy(), path.copy())
                if result:
                    return result
        
        for l in range(num_destinations):
            if l != j and allocation[i][l] > 0 and (i, l) not in visited:
                result = find_cycle(i, l, visited.copy(), path.copy())
                if result:
                    return result
        
        return None
    
    def calculate_opportunity_cost(i, j):
        if allocation[i][j] > 0:
            return 0  # Case déjà allouée
        
        # Trouver un cycle pour cette case vide
        cycle = find_cycle(i, j)
        if not cycle:
            return float('inf')  # Pas de cycle trouvé
        
        # Calculer le coût marginal
        cost = 0
        sign = 1
        for (x, y) in cycle:
            cost += sign * cost_matrix[x][y]
            sign *= -1
        
        return cost
    
    improved = True
    iterations = 0
    
    while improved and iterations < 100:  # Limite d'itérations pour éviter les boucles infinies
        improved = False
        iterations += 1
        
        # Étape 1: Calculer les coûts d'opportunité pour chaque case vide
        opportunity_costs = []
        for i in range(num_sources):
            for j in range(num_destinations):
                if allocation[i][j] == 0:  # Case vide
                    cost = calculate_opportunity_cost(i, j)
                    opportunity_costs.append((cost, i, j))
        
        # Trier par coût d'opportunité (le plus négatif en premier)
        opportunity_costs.sort()
        
        # Étape 2: Trouver la meilleure amélioration possible
        for cost, i, j in opportunity_costs:
            if cost >= 0:
                break  # Pas d'amélioration possible
                
            # Trouver le cycle pour cette case
            cycle = find_cycle(i, j)
            if not cycle:
                continue
                
            # Trouver la quantité maximale à déplacer
            min_qty = float('inf')
            sign = -1
            for idx in range(1, len(cycle)):
                x, y = cycle[idx]
                if sign == -1:  # Cases où on soustrait
                    min_qty = min(min_qty, allocation[x][y])
                sign *= -1
            
            # Appliquer les changements
            sign = 1
            for idx in range(len(cycle)):
                x, y = cycle[idx]
                if sign == 1:  # Cases où on ajoute
                    allocation[x][y] += min_qty
                else:  # Cases où on soustrait
                    allocation[x][y] -= min_qty
                sign *= -1
            
            improved = True
            break
    
    total_cost = calculate_transport_cost(allocation, cost_matrix)
    return allocation, total_cost

# --------- Interface graphique ---------
class NetworkOptimizerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Optimisation du chemin - Réseau Télécom")
        self.geometry("1200x800")

        # Frame principal avec scrollbar
        main_frame = tk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Configuration des routeurs
        config_frame = tk.LabelFrame(main_frame, text="Configuration", padx=10, pady=10)
        config_frame.pack(fill=tk.X, pady=5)

        # Liste déroulante des cas d'usage réseau
        tk.Label(config_frame, text="Cas d'usage réseau :").grid(row=0, column=0, sticky="w")
        self.use_case_var = tk.StringVar()
        use_cases = ttk.Combobox(config_frame, textvariable=self.use_case_var, width=30)
        use_cases['values'] = [
            "Routage simple",
            "Déploiement du réseau",
            "Optimisation du flux",
            "Affectation des canaux",
            "Répartition du trafic"
        ]
        use_cases.grid(row=0, column=1, padx=5)
        use_cases.bind("<<ComboboxSelected>>", self.on_use_case_selected)
        use_cases.current(0)

        tk.Label(config_frame, text="Nombre de routeurs (R) :").grid(row=1, column=0, sticky="w")
        self.num_routers_var = tk.StringVar()
        tk.Entry(config_frame, textvariable=self.num_routers_var, width=10).grid(row=1, column=1, padx=5)

        # Bouton modifié pour générer et afficher le graphe
        tk.Button(config_frame, text="Générer et afficher le graphe", 
                 command=self.generate_and_show_graph, bg="lightblue").grid(row=1, column=2, padx=10)

        tk.Label(config_frame, text="Source (ex: R1) :").grid(row=2, column=0, sticky="w")
        self.source_var = tk.StringVar()
        tk.Entry(config_frame, textvariable=self.source_var, width=10).grid(row=2, column=1, padx=5)

        tk.Label(config_frame, text="Puits (pour Ford-Fulkerson, ex: R5) :").grid(row=3, column=0, sticky="w")
        self.sink_var = tk.StringVar()
        tk.Entry(config_frame, textvariable=self.sink_var, width=10).grid(row=3, column=1, padx=5)

        # Boutons d'algorithmes
        buttons_frame = tk.LabelFrame(main_frame, text="Algorithmes", padx=10, pady=10)
        buttons_frame.pack(fill=tk.X, pady=5)

        # Première ligne de boutons
        frame_buttons1 = tk.Frame(buttons_frame)
        frame_buttons1.pack(pady=5)

        self.dijkstra_btn = tk.Button(frame_buttons1, text="Dijkstra", command=self.run_dijkstra, 
                                    bg="lightgreen", width=12)
        self.dijkstra_btn.grid(row=0, column=0, padx=5)
        
        self.bellman_btn = tk.Button(frame_buttons1, text="Bellman-Ford", command=self.run_bellman_ford, 
                                   bg="lightgreen", width=12)
        self.bellman_btn.grid(row=0, column=1, padx=5)
        
        self.kruskal_btn = tk.Button(frame_buttons1, text="Kruskal", command=self.run_kruskal, 
                                   bg="lightcoral", width=12)
        self.kruskal_btn.grid(row=0, column=2, padx=5)
        
        self.welsh_btn = tk.Button(frame_buttons1, text="Welsh-Powell", command=self.run_welsh_powell, 
                                 bg="lightcoral", width=12)
        self.welsh_btn.grid(row=0, column=3, padx=5)

        # Deuxième ligne de boutons
        frame_buttons2 = tk.Frame(buttons_frame)
        frame_buttons2.pack(pady=5)

        self.ford_btn = tk.Button(frame_buttons2, text="Ford-Fulkerson", command=self.run_ford_fulkerson, 
                                bg="lightyellow", width=12)
        self.ford_btn.grid(row=0, column=0, padx=5)
        
        self.metra_btn = tk.Button(frame_buttons2, text="Potentiel Métra", command=self.run_potentiel_metra, 
                                 bg="lightyellow", width=12)
        self.metra_btn.grid(row=0, column=1, padx=5)
        
        self.nord_ouest_btn = tk.Button(frame_buttons2, text="Nord-Ouest", command=self.run_nord_ouest, 
                                      bg="lightpink", width=12)
        self.nord_ouest_btn.grid(row=0, column=2, padx=5)
        
        self.moindre_cout_btn = tk.Button(frame_buttons2, text="Moindre Coût", command=self.run_moindre_cout, 
                                       bg="lightpink", width=12)
        self.moindre_cout_btn.grid(row=0, column=3, padx=5)
        
        self.stepping_btn = tk.Button(frame_buttons2, text="Stepping Stone", command=self.run_stepping_stone, 
                                    bg="lightpink", width=12)
        self.stepping_btn.grid(row=0, column=4, padx=5)

        # Zone de sortie
        output_frame = tk.LabelFrame(main_frame, text="Résultats", padx=10, pady=10)
        output_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Scrollbar pour la zone de texte
        scrollbar = tk.Scrollbar(output_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.output = tk.Text(output_frame, height=25, yscrollcommand=scrollbar.set)
        self.output.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.output.yview)

        # Initialisation des variables
        self.nodes = []
        self.graph_directed = {}
        self.graph_undirected = {}
        self.current_transport_problem = None
        
        # Mise à jour initiale des boutons
        self.on_use_case_selected()

    def on_use_case_selected(self, event=None):
        use_case = self.use_case_var.get()
        
        # Réinitialiser tous les boutons
        for btn in [self.dijkstra_btn, self.bellman_btn, self.kruskal_btn, self.welsh_btn,
                   self.ford_btn, self.metra_btn, self.nord_ouest_btn, self.moindre_cout_btn,
                   self.stepping_btn]:
            btn.config(state=tk.NORMAL, bg="lightgray")
        
        # Activer les boutons appropriés selon le cas d'usage
        if use_case == "Routage simple":
            self.dijkstra_btn.config(bg="lightgreen")
            self.bellman_btn.config(bg="lightgreen")
        elif use_case == "Déploiement du réseau":
            self.kruskal_btn.config(bg="lightcoral")
            self.metra_btn.config(bg="lightyellow")
        elif use_case == "Optimisation du flux":
            self.ford_btn.config(bg="lightyellow")
        elif use_case == "Affectation des canaux":
            self.welsh_btn.config(bg="lightcoral")
        elif use_case == "Répartition du trafic":
            self.nord_ouest_btn.config(bg="lightpink")
            self.moindre_cout_btn.config(bg="lightpink")
            self.stepping_btn.config(bg="lightpink")

    def generate_and_show_graph(self):
        """Génère le graphe et l'affiche immédiatement"""
        try:
            n = int(self.num_routers_var.get())
            if n < 2 or n > 100:
                raise ValueError("Entre 2 et 100 routeurs.")
        except Exception as e:
            messagebox.showerror("Erreur", f"Entrée invalide : {e}")
            return
        
        self.nodes = [f"R{i+1}" for i in range(n)]
        self.graph_directed = generate_directed_graph(self.nodes)
        self.graph_undirected = generate_undirected_graph(self.nodes)
        
        self.output.delete(1.0, tk.END)
        self.output.insert(tk.END, f"=== GRAPHE GÉNÉRÉ ===\n")
        self.output.insert(tk.END, f"Routeurs: {', '.join(self.nodes)}\n\n")
        
        # Afficher le graphe dirigé
        self.output.insert(tk.END, "Graphe dirigé :\n")
        for node in self.graph_directed:
            neighbors = self.graph_directed[node]
            if neighbors:
                self.output.insert(tk.END, f"{node} → {', '.join(f'{n}({w})' for n, w in neighbors.items())}\n")
            else:
                self.output.insert(tk.END, f"{node} → aucun voisin\n")
        
        self.output.insert(tk.END, "\n")
        
        # Afficher le graphe non dirigé
        self.output.insert(tk.END, "Graphe non dirigé :\n")
        for node in self.graph_undirected:
            neighbors = self.graph_undirected[node]
            if neighbors:
                self.output.insert(tk.END, f"{node} ↔ {', '.join(f'{n}({w})' for n, w in neighbors.items())}\n")
            else:
                self.output.insert(tk.END, f"{node} ↔ aucun voisin\n")

    def run_dijkstra(self):
        source = self.source_var.get().strip()
        if source not in self.nodes:
            messagebox.showerror("Erreur", "Source invalide.")
            return
        
        distances = dijkstra(self.graph_directed, source)
        self.output.delete(1.0, tk.END)
        self.output.insert(tk.END, f"=== ALGORITHME DE DIJKSTRA ===\n")
        self.output.insert(tk.END, f"Plus courts chemins depuis {source} :\n\n")
        
        for k, v in sorted(distances.items()):
            distance_str = str(v) if v != float('inf') else "∞"
            self.output.insert(tk.END, f"{source} → {k} : {distance_str}\n")

    def run_bellman_ford(self):
        source = self.source_var.get().strip()
        if source not in self.nodes:
            messagebox.showerror("Erreur", "Source invalide.")
            return
        
        try:
            distances = bellman_ford(self.graph_directed, source)
            self.output.delete(1.0, tk.END)
            self.output.insert(tk.END, f"=== ALGORITHME DE BELLMAN-FORD ===\n")
            self.output.insert(tk.END, f"Plus courts chemins depuis {source} :\n\n")
            
            for k, v in sorted(distances.items()):
                distance_str = str(v) if v != float('inf') else "∞"
                self.output.insert(tk.END, f"{source} → {k} : {distance_str}\n")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def run_kruskal(self):
        mst, weight = kruskal(self.graph_undirected)
        self.output.delete(1.0, tk.END)
        self.output.insert(tk.END, f"=== ALGORITHME DE KRUSKAL (MST) ===\n")
        self.output.insert(tk.END, f"Arbre couvrant minimal :\n\n")
        
        for u, v, w in mst:
            self.output.insert(tk.END, f"{u} ←→ {v} : {w}\n")
        self.output.insert(tk.END, f"\nPoids total de l'arbre : {weight}\n")

    def run_welsh_powell(self):
        colors = welsh_powell(self.graph_undirected)
        self.output.delete(1.0, tk.END)
        self.output.insert(tk.END, f"=== ALGORITHME DE WELSH-POWELL ===\n")
        self.output.insert(tk.END, f"Coloration des sommets :\n\n")
        
        # Grouper par couleur
        color_groups = {}
        for node, color in colors.items():
            if color not in color_groups:
                color_groups[color] = []
            color_groups[color].append(node)
        
        for color in sorted(color_groups.keys()):
            nodes_str = ', '.join(sorted(color_groups[color]))
            self.output.insert(tk.END, f"Couleur {color} : {nodes_str}\n")
        
        self.output.insert(tk.END, f"\nNombre total de couleurs utilisées : {len(color_groups)}\n")

    def run_ford_fulkerson(self):
        source = self.source_var.get().strip()
        sink = self.sink_var.get().strip()
        if source not in self.nodes or sink not in self.nodes:
            messagebox.showerror("Erreur", "Source ou puits invalide.")
            return
        
        max_flow, _ = ford_fulkerson(self.graph_directed, source, sink)
        self.output.delete(1.0, tk.END)
        self.output.insert(tk.END, f"=== ALGORITHME DE FORD-FULKERSON ===\n")
        self.output.insert(tk.END, f"Flux maximum de {source} vers {sink} : {max_flow}\n")

    def run_potentiel_metra(self):
        try:
            earliest, latest, marge = potentiel_metra(self.graph_directed)
            self.output.delete(1.0, tk.END)
            self.output.insert(tk.END, "=== MÉTHODE DU POTENTIEL MÉTRA ===\n")
            self.output.insert(tk.END, "Analyse des tâches du projet :\n\n")
            
            self.output.insert(tk.END, f"{'Tâche':<8} {'Au plus tôt':<12} {'Au plus tard':<12} {'Marge':<8} {'Critique'}\n")
            self.output.insert(tk.END, "-" * 60 + "\n")
            
            for node in sorted(self.nodes):
                early = earliest.get(node, 0)
                late = latest.get(node, 0)
                margin = marge.get(node, 0)
                critical = "OUI" if margin == 0 else "NON"
                
                self.output.insert(tk.END, f"{node:<8} {early:<12} {late:<12} {margin:<8} {critical}\n")
                
        except Exception as e:
            messagebox.showerror("Erreur", f"Erreur dans le calcul Potentiel Métra : {e}")

    def run_nord_ouest(self):
        self.current_transport_problem = generate_transport_problem()
        supply, demand, cost_matrix = self.current_transport_problem
        allocation = north_west_corner_method(supply, demand)
        total_cost = calculate_transport_cost(allocation, cost_matrix)
        self.display_transport_results("MÉTHODE DU COIN NORD-OUEST", supply, demand, cost_matrix, allocation, total_cost)

    def run_moindre_cout(self):
        self.current_transport_problem = generate_transport_problem()
        supply, demand, cost_matrix = self.current_transport_problem
        allocation = moindre_cout_method(supply, demand, cost_matrix)
        total_cost = calculate_transport_cost(allocation, cost_matrix)
        self.display_transport_results("MÉTHODE DU MOINDRE COÛT", supply, demand, cost_matrix, allocation, total_cost)

    def run_stepping_stone(self):
        if not self.current_transport_problem:
            messagebox.showwarning("Avertissement", "Veuillez d'abord générer un problème de transport avec Nord-Ouest ou Moindre Coût.")
            return
        
        supply, demand, cost_matrix = self.current_transport_problem
        initial_allocation = moindre_cout_method(supply, demand, cost_matrix)
        optimized_allocation, total_cost = stepping_stone_method(supply, demand, cost_matrix, initial_allocation)
        
        self.display_transport_results("MÉTHODE STEPPING STONE (OPTIMISATION)", supply, demand, cost_matrix, optimized_allocation, total_cost)

    def display_transport_results(self, method_name, supply, demand, cost_matrix, allocation, total_cost):
        num_sources = len(supply)
        num_destinations = len(demand)
        
        self.output.delete(1.0, tk.END)
        self.output.insert(tk.END, f"=== {method_name} ===\n")
        self.output.insert(tk.END, "Problème de transport résolu\n\n")
        
        # Affichage des données du problème
        self.output.insert(tk.END, "DONNÉES DU PROBLÈME :\n")
        self.output.insert(tk.END, f"Capacités d'offre (sources) : {supply}\n")
        self.output.insert(tk.END, f"Demandes (destinations) : {demand}\n")
        self.output.insert(tk.END, f"Offre totale = Demande totale = {sum(supply)}\n\n")
        
        # Affichage de la matrice de coûts
        self.output.insert(tk.END, "MATRICE DES COÛTS DE TRANSPORT :\n")
        self.output.insert(tk.END, "     ")
        for j in range(num_destinations):
            dest_name = f"D{j+1}" if j < num_destinations - 1 or num_destinations <= 4 else "Fict"
            self.output.insert(tk.END, f"{dest_name:>6}")
        self.output.insert(tk.END, "\n")
        
        for i in range(num_sources):
            source_name = f"S{i+1}" if i < num_sources - 1 or num_sources <= 4 else "Fict"
            self.output.insert(tk.END, f"{source_name:>4} ")
            for j in range(num_destinations):
                self.output.insert(tk.END, f"{cost_matrix[i][j]:>6}")
            self.output.insert(tk.END, "\n")
        
        # Affichage de la solution (allocation)
        self.output.insert(tk.END, "\nSOLUTION (ALLOCATION) :\n")
        self.output.insert(tk.END, "     ")
        for j in range(num_destinations):
            dest_name = f"D{j+1}" if j < num_destinations - 1 or num_destinations <= 4 else "Fict"
            self.output.insert(tk.END, f"{dest_name:>6}")
        self.output.insert(tk.END, f"{'Offre':>8}\n")
        
        for i in range(num_sources):
            source_name = f"S{i+1}" if i < num_sources - 1 or num_sources <= 4 else "Fict"
            self.output.insert(tk.END, f"{source_name:>4} ")
            for j in range(num_destinations):
                self.output.insert(tk.END, f"{allocation[i][j]:>6}")
            used_supply = sum(allocation[i])
            self.output.insert(tk.END, f"{used_supply:>8}\n")
        
        # Ligne des demandes satisfaites
        self.output.insert(tk.END, "Dem. ")
        for j in range(num_destinations):
            satisfied_demand = sum(allocation[i][j] for i in range(num_sources))
            self.output.insert(tk.END, f"{satisfied_demand:>6}")
        self.output.insert(tk.END, "\n")
        
        # Calcul et affichage du coût total
        self.output.insert(tk.END, f"\nCOÛT TOTAL DE TRANSPORT : {total_cost} unités\n")
        
        # Détail du calcul du coût
        self.output.insert(tk.END, "\nDÉTAIL DU CALCUL DU COÛT :\n")
        for i in range(num_sources):
            for j in range(num_destinations):
                if allocation[i][j] > 0:
                    source_name = f"S{i+1}" if i < num_sources - 1 or num_sources <= 4 else "Source fictive"
                    dest_name = f"D{j+1}" if j < num_destinations - 1 or num_destinations <= 4 else "Destination fictive"
                    cost_detail = allocation[i][j] * cost_matrix[i][j]
                    self.output.insert(tk.END, f"{source_name} → {dest_name} : {allocation[i][j]} × {cost_matrix[i][j]} = {cost_detail}\n")

if __name__ == "__main__":
    app = NetworkOptimizerApp()
    app.mainloop()