#!/usr/bin/env python3
"""Exact check of 12-vertex counterexamples found by vt_search.py: a circulant on Z12 and a Cayley
graph on the dihedral group D6 (order 12) that are cospectral, non-isomorphic, connected and
vertex-transitive (hence walk-regular), so their local energies coincide exactly."""
import itertools
import networkx as nx
import sympy as sp
import numpy as np

m = 6
D = [(i, j) for i in range(m) for j in range(2)]         # r^i s^j, s r = r^-1 s
def mul(a, b):
    i1, j1 = a; i2, j2 = b
    return ((i1 + (i2 if j1 == 0 else -i2)) % m, (j1 + j2) % 2)
def inv(a):
    return next(b for b in D if mul(a, b) == (0, 0))
def cay_D(S):
    G = nx.Graph(); G.add_nodes_from(D)
    G.add_edges_from((g, mul(g, s)) for g in D for s in S)
    return G
def circ(n, S):
    G = nx.Graph(); G.add_nodes_from(range(n))
    G.add_edges_from((i, (i + s) % n) for i in range(n) for s in S)
    return G

x = sp.symbols('x')
def cp(G):
    A = sp.Matrix(nx.to_numpy_array(G, nodelist=list(G.nodes()), dtype=int).tolist())
    return sp.expand(A.charpoly(x).as_expr()), A
def deck(A):
    n = A.shape[0]
    return [sp.expand(A.extract([k for k in range(n) if k != v], [k for k in range(n) if k != v]).charpoly(x).as_expr()) for v in range(n)]

# enumerate circulants on Z12 and Cayley graphs on D6, find cospectral non-isomorphic connected pairs
circs = []
pairs12 = [frozenset({s, (12 - s) % 12}) for s in range(1, 7)]
for r in range(1, 7):
    for sub in itertools.combinations(pairs12, r):
        S = set().union(*sub)
        G = circ(12, S)
        if nx.is_connected(G): circs.append((sorted(S), G))
classes = []
for g in D:
    if g == (0, 0): continue
    c = frozenset({g, inv(g)})
    if c not in classes: classes.append(c)
found = []
for r in range(1, len(classes) + 1):
    for sub in itertools.combinations(classes, r):
        S = set().union(*sub)
        H = cay_D(S)
        if not nx.is_connected(H): continue
        sH = np.round(np.sort(np.linalg.eigvalsh(nx.to_numpy_array(H))), 8)
        for Sc, G in circs:
            sG = np.round(np.sort(np.linalg.eigvalsh(nx.to_numpy_array(G))), 8)
            if (sG == sH).all() and not nx.is_isomorphic(G, H):
                found.append((Sc, sorted(S), G, H))
print(len(found), "cospectral non-isomorphic (circulant on Z12, Cayley on D6) pairs (with repetitions)")
Sc, SH, G, H = min(found, key=lambda t: (len(t[0]), t[0]))
print("circulant Z12 connection set:", Sc)
print("D6 connection set (r^i s^j as (i,j)):", SH)
pG, AG = cp(G); pH, AH = cp(H)
print("charpoly G:", sp.factor(pG)); print("charpoly H:", sp.factor(pH)); print("equal:", pG == pH)
dG, dH = deck(AG), deck(AH)
print("all vertex-deleted charpolys equal (G):", len(set(dG)) == 1, " (H):", len(set(dH)) == 1, " same:", dG[0] == dH[0])
print("deleted charpoly:", sp.factor(dG[0]))
def energy(p):
    tot = 0
    for fac, mult in sp.factor_list(p)[1]:
        tot += mult * sum(abs(complex(r).real) for r in sp.Poly(fac, x).nroots(n=40))
    return tot
EG, Ed = energy(pG), energy(dG[0])
print("E(G) = %.12f, E(G-v) = %.12f, e(G) = e(H) = %.12f" % (EG, Ed, 12 * (EG - Ed)))
print("degrees:", set(dict(G.degree()).values()), set(dict(H.degree()).values()),
      " triangles:", sum(nx.triangles(G).values()) // 3, sum(nx.triangles(H).values()) // 3,
      " clique numbers:", max(len(c) for c in nx.find_cliques(G)), max(len(c) for c in nx.find_cliques(H)))
