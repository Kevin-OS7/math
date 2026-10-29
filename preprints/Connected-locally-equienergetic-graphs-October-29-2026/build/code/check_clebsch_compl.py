#!/usr/bin/env python3
"""Check that Cay(Z_4^2, {(0,±1),(0,2),(±1,0),(2,0),(±1,±1)}) is isomorphic to the complement of
the Clebsch graph (folded 5-cube), and record its exact spectral data."""
import itertools
import networkx as nx
import sympy as sp
C = {(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(1,1),(1,3),(3,1),(3,3)}
V = [(a, b) for a in range(4) for b in range(4)]
Q = nx.Graph(); Q.add_nodes_from(V)
Q.add_edges_from((x, y) for x in V for y in V if x < y and ((x[0]-y[0]) % 4, (x[1]-y[1]) % 4) in C)
W = list(itertools.product([0, 1], repeat=4))
gens = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(1,1,1,1)]
cl = nx.Graph(); cl.add_nodes_from(W)
cl.add_edges_from((x, tuple((a+b) % 2 for a, b in zip(x, g))) for x in W for g in gens)
print("Clebsch is SRG(16,5,0,2):", all(d == 5 for _, d in cl.degree()))
print("Q isomorphic to complement of Clebsch:", nx.is_isomorphic(Q, nx.complement(cl)))
x = sp.symbols('x')
A = sp.Matrix(16, 16, lambda i, j: 1 if Q.has_edge(V[i], V[j]) else 0)
print("charpoly Q:", sp.factor(A.charpoly(x).as_expr()))
dels = {sp.expand(A.extract([k for k in range(16) if k != v], [k for k in range(16) if k != v]).charpoly(x).as_expr()) for v in range(16)}
print("charpoly Q-v (all v):", [sp.factor(d) for d in dels])
A0 = A.extract(list(range(1, 16)), list(range(1, 16)))
print("traces Q:", (A**2).trace(), (A**3).trace(), " Q-0:", A0.trace(), (A0**2).trace(), (A0**3).trace())
R = sp.Matrix(16, 16, lambda i, j: 1 if V[i] != V[j] and (V[i][0] == V[j][0] or V[i][1] == V[j][1]) else 0)
R0 = R.extract(list(range(1, 16)), list(range(1, 16)))
print("traces R:", (R**2).trace(), (R**3).trace(), " R-0:", R0.trace(), (R0**2).trace(), (R0**3).trace())
print("minpoly checks:",
      (A - 10*sp.eye(16))*(A - 2*sp.eye(16))*(A + 2*sp.eye(16)) == sp.zeros(16),
      (A0 - 2*sp.eye(15))*(A0 + 2*sp.eye(15))*(A0**2 - 10*A0 + 6*sp.eye(15)) == sp.zeros(15),
      (R0 - 2*sp.eye(15))*(R0 + 2*sp.eye(15))*(R0**2 - 6*R0 + 2*sp.eye(15)) == sp.zeros(15))
