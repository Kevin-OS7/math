#!/usr/bin/env python3
"""Exact spectral data of the order-10 pair used in Proof10.lean."""
import networkx as nx, sympy as sp
EG = [(0,4),(0,5),(1,4),(1,6),(1,8),(1,9),(2,5),(2,7),(2,8),(2,9),(3,6),(3,7),(4,8),(5,8),(6,9),(7,9)]
EH = [(0,3),(0,6),(0,7),(1,4),(1,6),(1,7),(2,5),(2,8),(3,6),(3,8),(3,9),(4,7),(4,8),(4,9),(5,9),(8,9)]
G = nx.Graph(EG); H = nx.Graph(EH)
x = sp.symbols('x')
def cp(Gr, nodes):
    return sp.factor(sp.Matrix(len(nodes), len(nodes), lambda i, j: int(Gr.has_edge(nodes[i], nodes[j]))).charpoly(x).as_expr())
V = list(range(10))
print("phi(G) =", cp(G, V)); print("phi(H) =", cp(H, V))
print("phi(co-G) == phi(co-H):", sp.expand(cp(nx.complement(G), V) - cp(nx.complement(H), V)) == 0)
pi = [2, 3, 4, 5, 0, 1, 7, 6, 9, 8]
for v in V:
    a = cp(G, [u for u in V if u != v]); b = cp(H, [u for u in V if u != pi[v]])
    assert sp.expand(a - b) == 0
print("phi(G - v) == phi(H - pi(v)) for all v, pi =", pi)
import mpmath as mp
mp.mp.dps = 40
def E(Gr, nodes):
    A = mp.matrix([[int(Gr.has_edge(a, b)) for b in nodes] for a in nodes])
    return sum(abs(t) for t in mp.eigsy(A, eigvals_only=True))
eG = 10 * E(G, V) - sum(E(G, [u for u in V if u != v]) for v in V)
eH = 10 * E(H, V) - sum(E(H, [u for u in V if u != v]) for v in V)
print("E(G) =", mp.nstr(E(G, V), 20), " e(G) =", mp.nstr(eG, 25), " e(H) =", mp.nstr(eH, 25))
print("degree sequences:", sorted(d for _, d in G.degree()), sorted(d for _, d in H.degree()))
print("diameters:", nx.diameter(G), nx.diameter(H))
