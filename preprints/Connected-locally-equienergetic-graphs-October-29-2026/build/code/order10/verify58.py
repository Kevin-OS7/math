#!/usr/bin/env python3
"""Independent check of the 58 order-10 pairs in pairs10.txt: connectivity, non-isomorphism,
equal characteristic polynomials, equal multisets of vertex-deleted characteristic polynomials
(= same eigenvalues and angles), equal degree sequences, cospectral complements, edge counts,
and whether the pair is related by a single Godsil-McKay switching (set size 4)."""
import itertools, sys
import networkx as nx
import sympy as sp

def g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - b)) & 1 for b in range(6)]
    G = nx.Graph(); G.add_nodes_from(range(n)); k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: G.add_edge(i, j)
            k += 1
    return G

x = sp.symbols('x')
def cp(G, nodes):
    return sp.Poly(sp.Matrix(len(nodes), len(nodes), lambda i, j: int(G.has_edge(nodes[i], nodes[j]))).charpoly(x).as_expr(), x).all_coeffs()

def gm4(G, H):
    n = G.number_of_nodes()
    for C in itertools.combinations(range(n), 4):
        if len({d for _, d in G.subgraph(C).degree()}) != 1: continue
        ok = True
        for u in range(n):
            if u in C: continue
            t = sum(G.has_edge(u, c) for c in C)
            if t not in (0, 2, 4): ok = False; break
        if not ok: continue
        G2 = G.copy()
        for u in range(n):
            if u in C: continue
            if sum(G.has_edge(u, c) for c in C) == 2:
                for c in C:
                    if G.has_edge(u, c): G2.remove_edge(u, c)
                    else: G2.add_edge(u, c)
        if nx.is_isomorphic(G2, H): return True
    return False

pairs = [l.split() for l in open(sys.argv[1]) if l.strip()]
stats = dict(n=len(pairs), conn=0, noniso=0, cp=0, deck=0, deg=0, cocp=0, gm4=0)
edges = []
for a, b in pairs:
    G, H = g6(a), g6(b)
    V = list(range(G.number_of_nodes()))
    stats['conn'] += nx.is_connected(G) and nx.is_connected(H)
    stats['noniso'] += not nx.is_isomorphic(G, H)
    stats['cp'] += cp(G, V) == cp(H, V)
    dG = sorted(tuple(cp(G, [u for u in V if u != v])) for v in V)
    dH = sorted(tuple(cp(H, [u for u in V if u != v])) for v in V)
    stats['deck'] += dG == dH
    stats['deg'] += sorted(d for _, d in G.degree()) == sorted(d for _, d in H.degree())
    stats['cocp'] += cp(nx.complement(G), V) == cp(nx.complement(H), V)
    stats['gm4'] += gm4(G, H)
    edges.append((G.number_of_edges(), H.number_of_edges(), a, b))
print(stats)
print("edge counts (min, max):", min(e[0] for e in edges), max(e[0] for e in edges))
print("pairs with fewest edges:", [e for e in edges if e[0] == min(x[0] for x in edges)])
