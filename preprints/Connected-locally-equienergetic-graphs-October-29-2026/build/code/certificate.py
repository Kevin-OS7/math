#!/usr/bin/env python3
"""Build an integer intertwiner P with  P*A_R = A_S*P,  P*P^T = 4I,  P fixing vertex (0,0)
(row/column (0,0) of P equal 2*e_(0,0)), from a Godsil-McKay switching of the rook graph R
w.r.t. a transversal C avoiding (0,0), followed by an isomorphism onto S fixing (0,0)."""
import itertools
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

V = [(a, b) for a in range(4) for b in range(4)]
I = {v: i for i, v in enumerate(V)}
def adjR(x, y): return x != y and (x[0] == y[0] or x[1] == y[1])
CS = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
def adjS(x, y): return ((x[0] - y[0]) % 4, (x[1] - y[1]) % 4) in CS
AR = np.array([[int(adjR(x, y)) for y in V] for x in V])
AS = np.array([[int(adjS(x, y)) for y in V] for x in V])

def gm(C):
    C = [I[c] for c in C]
    Q = 2 * np.eye(16, dtype=int)
    for i in C:
        for j in C:
            Q[i, j] = 1 if i != j else -1
    return Q

results = []
for perm in itertools.permutations(range(4)):
    C = [(a, perm[a]) for a in range(4)]
    if (0, 0) in C: continue
    Q = gm(C)
    B = (Q @ AR @ Q) // 4
    assert ((Q @ AR @ Q) % 4 == 0).all()
    GB, GS = nx.from_numpy_array(B), nx.from_numpy_array(AS)
    gmatch = GraphMatcher(GB, GS)
    for iso in gmatch.isomorphisms_iter():   # iso: vertex of B -> vertex of S
        if iso[0] != 0: continue
        Pi = np.zeros((16, 16), dtype=int)
        for u, w in iso.items():
            Pi[w, u] = 1       # Pi e_u = e_w
        P = Pi @ Q
        assert (P @ AR == AS @ P).all()
        assert (P @ P.T == 4 * np.eye(16, dtype=int)).all()
        assert P[0, 0] == 2 and (P[0, 1:] == 0).all() and (P[1:, 0] == 0).all()
        # check whether iso is affine:  w = M u + t over Z_4
        results.append((C, iso, P))
print(len(results), "certificates found")

def is_affine(iso):
    # iso maps index -> index; check map (a,b) -> M (a,b) mod 4 (it fixes 0, so linear)
    f = {V[u]: V[w] for u, w in iso.items()}
    e1, e2 = f[(1, 0)], f[(0, 1)]
    for (a, b), (c, d) in f.items():
        if ((a * e1[0] + b * e2[0]) % 4, (a * e1[1] + b * e2[1]) % 4) != (c, d):
            return False
    return True
aff = [r for r in results if is_affine(r[1])]
print(len(aff), "with linear isomorphism")
C, iso, P = (aff or results)[0]
print("C =", C)
print("iso (as map on Z4^2):", {V[u]: V[w] for u, w in sorted(iso.items())})
print(P)
np.save('P.npy', P)
