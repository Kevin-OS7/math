#!/usr/bin/env python3
"""Numerical exploration: local energies of assorted vertex-transitive / strongly regular graphs,
looking for NON-cospectral connected pairs of equal order with equal local energy."""
import itertools, math
import numpy as np
import networkx as nx

def e_local(G):
    A = nx.to_numpy_array(G, nodelist=sorted(G.nodes()))
    n = len(A)
    E = np.abs(np.linalg.eigvalsh(A)).sum()
    Ed = [np.abs(np.linalg.eigvalsh(np.delete(np.delete(A, v, 0), v, 1))).sum() for v in range(n)]
    return n * E - sum(Ed), E, np.round(np.linalg.eigvalsh(A), 6)

def cay_z4(C):
    G = nx.Graph()
    V = [(a, b) for a in range(4) for b in range(4)]
    G.add_nodes_from(V)
    for x in V:
        for y in V:
            d = ((x[0]-y[0]) % 4, (x[1]-y[1]) % 4)
            if x != y and d in C: G.add_edge(x, y)
    return G

graphs = {}
graphs['rook4x4'] = nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(4))
graphs['shrikhande'] = cay_z4({(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)})
# Clebsch graph: folded 5-cube = Cayley graph on Z2^4 with generators e1..e4, 1111
V = list(itertools.product([0,1], repeat=4))
gens = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(1,1,1,1)]
cl = nx.Graph(); cl.add_nodes_from(V)
for x in V:
    for g in gens:
        cl.add_edge(x, tuple((a+b) % 2 for a, b in zip(x, g)))
graphs['clebsch'] = cl
graphs['clebsch_complement'] = nx.complement(cl)
graphs['T6=L(K6)'] = nx.line_graph(nx.complete_graph(6))
graphs['K3xK5'] = nx.cartesian_product(nx.complete_graph(3), nx.complete_graph(5))
graphs['K3xK4'] = nx.cartesian_product(nx.complete_graph(3), nx.complete_graph(4))
graphs['L(Petersen)'] = nx.line_graph(nx.petersen_graph())
graphs['L(cube)'] = nx.line_graph(nx.hypercube_graph(3))
graphs['K15'] = nx.complete_graph(15); graphs['C15'] = nx.cycle_graph(15)
graphs['K16'] = nx.complete_graph(16); graphs['K12'] = nx.complete_graph(12)
graphs['K2xK8'] = nx.cartesian_product(nx.complete_graph(2), nx.complete_graph(8))
graphs['K4xK4 complement'] = nx.complement(graphs['rook4x4'])
graphs['hypercube Q4'] = nx.hypercube_graph(4)
graphs['K_{4,4,4,4}'] = nx.complete_multipartite_graph(4,4,4,4)
graphs['K_{8,8}'] = nx.complete_bipartite_graph(8,8)
for name, G in graphs.items():
    G = nx.convert_node_labels_to_integers(G)
    e, E, ev = e_local(G)
    vals, cnt = np.unique(ev, return_counts=True)
    print(f"{name:22s} n={G.number_of_nodes():2d} conn={nx.is_connected(G)!s:5s} E={E:9.4f} e={e:10.5f} spec={dict(zip(vals.tolist(), cnt.tolist()))}")
