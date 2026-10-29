#!/usr/bin/env python3
"""Exploration (not part of the proof): local energies of connected vertex-transitive graphs of
order n <= 16 obtained as Cayley graphs of all groups of order <= 15 (plus several groups of order
16) and the non-Cayley VT graphs of order <= 15 (Petersen, its complement, J(6,2), L(Petersen) and
their complements).  For a VT graph e(G) = n (E(G) - E(G - v)).  Reports coincidences of e among
non-isomorphic connected graphs of the same order."""
import itertools, sys
import numpy as np
import networkx as nx

def cyclic(n): return [(i,) for i in range(n)], lambda a, b: ((a[0] + b[0]) % n,)
def prod(*gs):
    els = [sum(t, ()) for t in itertools.product(*[g[0] for g in gs])]
    lens = [len(g[0][0]) for g in gs]
    def mul(a, b):
        out, k = (), 0
        for (E, m), L in zip(gs, lens):
            out += m(a[k:k+L], b[k:k+L]); k += L
        return out
    return els, mul
def dihedral(m):  # (r, s): r^i s^j ; s r = r^-1 s
    els = [(i, j) for i in range(m) for j in range(2)]
    def mul(a, b):
        i1, j1 = a; i2, j2 = b
        return (((i1 + (i2 if j1 == 0 else -i2)) % m), (j1 + j2) % 2)
    return els, mul
def dicyclic(m):  # Dic_m of order 4m: a^i x^j, a^{2m}=1, x^2=a^m, x a x^-1 = a^-1
    els = [(i, j) for i in range(2 * m) for j in range(2)]
    def mul(a, b):
        i1, j1 = a; i2, j2 = b
        i = (i1 + (i2 if j1 == 0 else -i2)) % (2 * m)
        if j1 == 1 and j2 == 1: i = (i + m) % (2 * m)
        return (i, (j1 + j2) % 2)
    return els, mul
def a4():
    pts = range(4)
    from itertools import permutations
    ev = [p for p in permutations(pts) if sum(p[i] > p[j] for i in range(4) for j in range(i+1, 4)) % 2 == 0]
    return ev, lambda a, b: tuple(a[b[i]] for i in range(4))
def semidihedral16():  # SD16: a^8=1, x^2=1, x a x = a^3
    els = [(i, j) for i in range(8) for j in range(2)]
    def mul(a, b):
        i1, j1 = a; i2, j2 = b
        return ((i1 + (i2 if j1 == 0 else 3 * i2)) % 8, (j1 + j2) % 2)
    return els, mul

groups = {}
for n in range(2, 16): groups[f'Z{n}'] = cyclic(n)
groups['Z2xZ2'] = prod(cyclic(2), cyclic(2)); groups['Z2xZ4'] = prod(cyclic(2), cyclic(4))
groups['Z2^3'] = prod(cyclic(2), cyclic(2), cyclic(2)); groups['Z3xZ3'] = prod(cyclic(3), cyclic(3))
groups['Z2xZ6'] = prod(cyclic(2), cyclic(6))
for m in range(3, 8): groups[f'D{m}'] = dihedral(m)
groups['Q8'] = dicyclic(2); groups['Dic3'] = dicyclic(3); groups['A4'] = a4()
# a few groups of order 16 (where we know the answer: R, S, Q are Cayley on Z4xZ4 / Z2^4)
groups['Z4xZ4'] = prod(cyclic(4), cyclic(4)); groups['Z2^4'] = prod(cyclic(2), cyclic(2), cyclic(2), cyclic(2))
groups['Z2xZ8'] = prod(cyclic(2), cyclic(8)); groups['Z16'] = cyclic(16); groups['D8'] = dihedral(8)
groups['SD16'] = semidihedral16(); groups['Q16'] = dicyclic(4); groups['Z2xD4'] = prod(cyclic(2), dihedral(4))

def local_energy_vt(A):
    n = len(A)
    E = np.abs(np.linalg.eigvalsh(A)).sum()
    Ev = np.abs(np.linalg.eigvalsh(A[1:, 1:])).sum()      # vertex 0 (VT: any vertex)
    return n * (E - Ev), E

def cayley_graphs(els, mul):
    idx = {g: i for i, g in enumerate(els)}
    n = len(els)
    e = next(g for g in els if all(mul(g, h) == h for h in els))
    inv = {g: next(h for h in els if mul(g, h) == e) for g in els}
    classes = []
    for g in els:
        if g == e: continue
        c = frozenset({g, inv[g]})
        if c not in classes: classes.append(c)
    for r in range(1, len(classes) + 1):
        for sub in itertools.combinations(classes, r):
            S = set().union(*sub)
            A = np.zeros((n, n))
            for g in els:
                for s in S:
                    A[idx[g], idx[mul(g, s)]] = 1
            yield A

graphs_by_n = {}
def add(A, name):
    G = nx.from_numpy_array(A)
    if not nx.is_connected(G): return
    n = len(A)
    e, E = local_energy_vt(A)
    spec = tuple(np.round(np.sort(np.linalg.eigvalsh(A)), 6))
    lst = graphs_by_n.setdefault(n, [])
    for (G2, e2, E2, spec2, names) in lst:
        if spec2 == spec and abs(e2 - e) < 1e-7 and nx.is_isomorphic(G, G2):
            names.add(name); return
    lst.append((G, e, E, spec, {name}))

for gname, (els, mul) in groups.items():
    for A in cayley_graphs(els, mul):
        add(A, gname)
P = nx.petersen_graph()
extra = {'Petersen': P, 'co-Petersen': nx.complement(P), 'J(6,2)': nx.line_graph(nx.complete_graph(6)),
         'co-J(6,2)': nx.complement(nx.line_graph(nx.complete_graph(6))), 'L(Petersen)': nx.line_graph(P),
         'co-L(Petersen)': nx.complement(nx.line_graph(P))}
for k, G in extra.items():
    add(nx.to_numpy_array(nx.convert_node_labels_to_integers(G)), k)

for n in sorted(graphs_by_n):
    lst = graphs_by_n[n]
    lst.sort(key=lambda t: t[1])
    coinc = []
    for i in range(len(lst)):
        for j in range(i + 1, len(lst)):
            if abs(lst[i][1] - lst[j][1]) < 1e-7:
                coinc.append((i, j))
    print(f"n={n:2d}: {len(lst):4d} connected VT graphs (iso classes found); coincidences of e: {len(coinc)}")
    for i, j in coinc:
        Gi, ei, Ei, si, ni = lst[i]; Gj, ej, Ej, sj, nj = lst[j]
        print(f"    e={ei:.9f}  E={Ei:.6f} vs {Ej:.6f}  cospectral={si == sj}  deg {Gi.degree(0)} vs {Gj.degree(0)}  groups {sorted(ni)[:3]} | {sorted(nj)[:3]}")
