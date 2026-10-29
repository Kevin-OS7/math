#!/usr/bin/env python3
"""Search for a Godsil-McKay switching set C in the 4x4 rook graph R
whose switching yields a graph isomorphic to the Shrikhande graph S."""
import itertools
import networkx as nx
import numpy as np

V = [(a, b) for a in range(4) for b in range(4)]
def adjR(x, y): return x != y and (x[0] == y[0] or x[1] == y[1])
CS = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
def adjS(x, y): return ((x[0] - y[0]) % 4, (x[1] - y[1]) % 4) in CS
AR = np.array([[1 if adjR(x, y) else 0 for y in V] for x in V])
AS = np.array([[1 if adjS(x, y) else 0 for y in V] for x in V])
GS = nx.from_numpy_array(AS)

found = []
for C in itertools.combinations(range(16), 4):
    sub = AR[np.ix_(C, C)]
    degs = set(sub.sum(1))
    if len(degs) != 1:
        continue
    ok = True
    for x in range(16):
        if x in C: continue
        k = AR[x, list(C)].sum()
        if k not in (0, 2, 4):
            ok = False; break
    if not ok: continue
    B = AR.copy()
    for x in range(16):
        if x in C: continue
        if AR[x, list(C)].sum() == 2:
            for c in C:
                B[x, c] = B[c, x] = 1 - AR[x, c]
    if (B != AR).any() and nx.is_isomorphic(nx.from_numpy_array(B), GS):
        found.append(C)
print(len(found), "switching sets of size 4 giving S; first few:", found[:10])
print([[V[i] for i in C] for C in found[:4]])
