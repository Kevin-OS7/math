#!/usr/bin/env python3
"""Exact verification of the rook / Shrikhande counterexample to
Dede--Popat Conjecture 1 (MATCH 93 (2025) 759-766).

Vertices: Z_4 x Z_4, encoded as 4*a+b.
R (4x4 rook graph):  x ~ y  iff x != y and (x1 == y1 or x2 == y2)
S (Shrikhande):      x ~ y  iff x - y in {+-(1,0), +-(0,1), +-(1,1)}
"""
import itertools, sys
import numpy as np
import networkx as nx
import sympy as sp

V = [(a, b) for a in range(4) for b in range(4)]
idx = {v: 4 * v[0] + v[1] for v in V}

def adjR(x, y):
    return x != y and (x[0] == y[0] or x[1] == y[1])

CS = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
def adjS(x, y):
    return ((x[0] - y[0]) % 4, (x[1] - y[1]) % 4) in CS

def matrix(adj):
    return sp.Matrix(16, 16, lambda i, j: 1 if adj(V[i], V[j]) else 0)

AR, AS = matrix(adjR), matrix(adjS)
for name, A in [("R", AR), ("S", AS)]:
    assert A == A.T and all(A[i, i] == 0 for i in range(16))
    assert all(sum(A.row(i)) == 6 for i in range(16)), "6-regular"
    # strongly regular (16,6,2,2): A^2 = 6I + 2A + 2(J - I - A)
    J = sp.ones(16, 16)
    assert A * A == 6 * sp.eye(16) + 2 * A + 2 * (J - sp.eye(16) - A)
print("both graphs are SRG(16,6,2,2)")

x = sp.symbols('x')
def charpoly(A):
    return sp.factor(A.charpoly(x).as_expr())

def deleted(A, v):
    keep = [i for i in range(A.shape[0]) if i != v]
    return A.extract(keep, keep)

def energy_exact(p):
    """sum of |roots| (with multiplicity) of a polynomial with real roots, exactly"""
    P = sp.Poly(p, x)
    tot = 0
    for r, m in sp.roots(P, multiple=False).items():
        tot += m * sp.Abs(r)
    assert sum(sp.roots(P, multiple=False).values()) == P.degree()
    return sp.nsimplify(sp.simplify(tot))

res = {}
for name, A in [("R", AR), ("S", AS)]:
    cp = charpoly(A)
    E = energy_exact(cp)
    dels = set()
    Edel = []
    for v in range(16):
        cpv = charpoly(deleted(A, v))
        dels.add(sp.expand(cpv))
        Edel.append(energy_exact(cpv))
    assert len(dels) == 1
    e = sum(E - Ev for Ev in Edel)
    res[name] = (sp.expand(cp), dels.pop(), E, Edel[0], sp.simplify(e))
    print(name, "charpoly =", cp)
    print(name, "charpoly(G-v) for all 16 v =", sp.factor(list(dels)[0]) if dels else sp.factor(res[name][1]))
    print(name, "E(G) =", E, " E(G-v) =", Edel[0], " e(G) =", sp.simplify(e))

assert res["R"][0] == res["S"][0] and res["R"][1] == res["S"][1]
assert res["R"][4] == res["S"][4] == 64
print("charpolys and deleted charpolys coincide; e(R) = e(S) = 64")

# numeric cross-check of energies with numpy
def num_e(A):
    A = np.array(A.tolist(), dtype=float)
    E = np.abs(np.linalg.eigvalsh(A)).sum()
    return sum(E - np.abs(np.linalg.eigvalsh(np.delete(np.delete(A, v, 0), v, 1))).sum() for v in range(16))
print("numeric e(R), e(S):", num_e(AR), num_e(AS))

GR = nx.Graph([(i, j) for i in range(16) for j in range(i + 1, 16) if AR[i, j]])
GS = nx.Graph([(i, j) for i in range(16) for j in range(i + 1, 16) if AS[i, j]])
print("connected:", nx.is_connected(GR), nx.is_connected(GS))
print("clique numbers:", max(len(c) for c in nx.find_cliques(GR)), max(len(c) for c in nx.find_cliques(GS)))
print("isomorphic?", nx.is_isomorphic(GR, GS))
print("diameters:", nx.diameter(GR), nx.diameter(GS))
