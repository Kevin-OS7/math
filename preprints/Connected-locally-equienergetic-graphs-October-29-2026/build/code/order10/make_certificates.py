#!/usr/bin/env python3
"""Certificates for the order-10 counterexample G = I?qa``kWo, H = ICOeeOwFG (Lean: Proof10.lean).

G has two disjoint Godsil-McKay switching sets C1 = {0,6,7,8}, C2 = {3,4,5,9}; switching G on
either gives a graph isomorphic to H.  With M_i = 2*diag(J/2 - I on C_i, I elsewhere) (integer,
M_i^2 = 4I) and sigma_i an isomorphism (switched graph) -> H, the integer matrix
P_i = Pi_{sigma_i} M_i satisfies  P_i A_G = A_H P_i  and  P_i P_i^T = 4 I.  For v outside C_i,
column v of P_i is 2 e_{sigma_i(v)} and row sigma_i(v) is 2 e_v^T, so deleting that row and column
gives a 9x9 certificate for G - v versus H - sigma_i(v).  We look for sigma_1, sigma_2 and a choice
i(v) with v not in C_{i(v)} such that pi(v) := sigma_{i(v)}(v) is a bijection.  Everything is
re-verified in exact integer arithmetic and printed as Lean literals."""
import itertools, sys
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

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

G, H = g6('I?qa``kWo'), g6('ICOeeOwFG')
n = 10
EG = [(0,4),(0,5),(1,4),(1,6),(1,8),(1,9),(2,5),(2,7),(2,8),(2,9),(3,6),(3,7),(4,8),(5,8),(6,9),(7,9)]
EH = [(0,3),(0,6),(0,7),(1,4),(1,6),(1,7),(2,5),(2,8),(3,6),(3,8),(3,9),(4,7),(4,8),(4,9),(5,9),(8,9)]
assert sorted(G.edges()) == EG and sorted(H.edges()) == EH
A = nx.to_numpy_array(G, nodelist=range(n), dtype=int)
B = nx.to_numpy_array(H, nodelist=range(n), dtype=int)
C1, C2 = (0, 6, 7, 8), (3, 4, 5, 9)

def switch(G, C):
    G2 = G.copy(); k = len(C)
    for u in range(n):
        if u in C: continue
        t = sum(1 for c in C if G.has_edge(u, c))
        assert t in (0, k // 2, k)
        if t == k // 2:
            for c in C:
                if G.has_edge(u, c): G2.remove_edge(u, c)
                else: G2.add_edge(u, c)
    return G2

def M(C):
    Mm = 2 * np.eye(n, dtype=int)
    for i in C:
        for j in C:
            Mm[i, j] = 1 if i != j else -1
    return Mm

G1, G2 = switch(G, C1), switch(G, C2)
isos1 = list(GraphMatcher(G1, H).isomorphisms_iter())
isos2 = list(GraphMatcher(G2, H).isomorphisms_iter())
print("isomorphisms G1->H:", len(isos1), " G2->H:", len(isos2))
best = None
for s1 in isos1:
    for s2 in isos2:
        for c in itertools.product((1, 2), repeat=2):          # choice for vertices 1 and 2
            choice = {v: 2 for v in C1}; choice.update({v: 1 for v in C2}); choice[1], choice[2] = c
            pi = [ (s1 if choice[v] == 1 else s2)[v] for v in range(n) ]
            if len(set(pi)) == n:
                best = (s1, s2, choice, pi); break
        if best: break
    if best: break
assert best, "no bijective assignment found"
s1, s2, choice, pi = best
def Pmat(s, C):
    Pi = np.zeros((n, n), dtype=int)
    for u, w in s.items(): Pi[w, u] = 1
    return Pi @ M(C)
P1, P2 = Pmat(s1, C1), Pmat(s2, C2)
for P in (P1, P2):
    assert (P @ A == B @ P).all() and (P @ P.T == 4 * np.eye(n, dtype=int)).all()
def succAbove(p, i):            # Fin.succAbove p i  (p : Fin 10, i : Fin 9)
    return i if i < p else i + 1
for v in range(n):
    P = P1 if choice[v] == 1 else P2
    w = pi[v]
    Pv = np.array([[P[succAbove(w, i), succAbove(v, j)] for j in range(n - 1)] for i in range(n - 1)])
    Av = np.array([[A[succAbove(v, i), succAbove(v, j)] for j in range(n - 1)] for i in range(n - 1)])
    Bw = np.array([[B[succAbove(w, i), succAbove(w, j)] for j in range(n - 1)] for i in range(n - 1)])
    assert (Pv @ Av == Bw @ Pv).all() and (Pv @ Pv.T == 4 * np.eye(n - 1, dtype=int)).all(), v
print("all 1 + 10 certificates verified;  pi =", pi, " choice =", [choice[v] for v in range(n)])

# BFS parent trees rooted at 0 (for connectivity) and a diamond in H
def parents(Gr):
    par = {0: 0}
    for u, w in nx.bfs_edges(Gr, 0): par[w] = u
    return [par[u] for u in range(n)]
parG, parH = parents(G), parents(H)
diamonds_H = [(a, b, c, d) for a, b, c, d in itertools.permutations(range(n), 4)
              if H.has_edge(a, b) and H.has_edge(a, c) and H.has_edge(b, c) and H.has_edge(a, d) and H.has_edge(b, d)]
diamonds_G = [t for t in itertools.permutations(range(n), 4)
              if G.has_edge(t[0], t[1]) and G.has_edge(t[0], t[2]) and G.has_edge(t[1], t[2]) and G.has_edge(t[0], t[3]) and G.has_edge(t[1], t[3])]
print("diamonds in G:", len(diamonds_G), " in H:", len(diamonds_H), " first in H:", diamonds_H[:1])

def lit(Mx):
    return "!![" + ";\n    ".join(", ".join(str(int(x)) for x in row) for row in Mx) + "]"
with open('certificates_lean.txt', 'w') as f:
    f.write("-- pi (deck bijection)\n![" + ", ".join(map(str, pi)) + "]\n")
    f.write("-- choice (1 -> P1, 2 -> P2)\n![" + ", ".join(str(choice[v]) for v in range(n)) + "]\n")
    f.write("-- parent G\n![" + ", ".join(map(str, parG)) + "]\n-- parent H\n![" + ", ".join(map(str, parH)) + "]\n")
    f.write("-- P1\n" + lit(P1) + "\n-- P2\n" + lit(P2) + "\n")
print(open('certificates_lean.txt').read())
