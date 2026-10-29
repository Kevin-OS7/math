#!/usr/bin/env python3
"""Rigorous classification of all candidate pairs from le_scan output (grouping tolerance T).
Every pair of graphs inside a group is classified:
  EXACT  - identical characteristic polynomial and identical multiset of vertex-deleted
           characteristic polynomials (exact integers): local energies are equal;
  UNEQUAL- otherwise, local energies recomputed with 30-digit arithmetic differ by > 1e-20.
Pairs not in a common group differ by more than T in double precision (error << T)."""
import sys, re, ast, itertools
from multiprocessing import Pool
import mpmath as mp
from hp_check import g6_adj
from exact_check import key

def hp_local(g):
    mp.mp.dps = 30
    A = g6_adj(g); n = len(A)
    def energy(B):
        return sum(abs(x) for x in mp.eigsy(mp.matrix(B), eigvals_only=True))
    E = energy(A)
    return n * E - sum(energy([[A[i][j] for j in range(n) if j != v] for i in range(n) if i != v]) for v in range(n))

def classify(gs):
    ks = {g: key(g) for g in gs}
    out = []
    vals = {}
    for a, b in itertools.combinations(gs, 2):
        if ks[a] == ks[b]:
            out.append(("EXACT", a, b, None))
        else:
            for g in (a, b):
                if g not in vals: vals[g] = hp_local(g)
            d = abs(vals[a] - vals[b])
            out.append(("UNEQUAL" if d > mp.mpf(10) ** -20 else "EQUAL_OTHER", a, b, mp.nstr(d, 4)))
    return out

if __name__ == "__main__":
    groups = []
    for line in open(sys.argv[1]):
        m = re.match(r'\s+e=(\S+) spread=(\S+) (\[.*\])', line)
        if m: groups.append([g for g, _ in ast.literal_eval(m.group(3))])
    with Pool(int(sys.argv[2]) if len(sys.argv) > 2 else 4) as pool:
        res = pool.map(classify, groups, chunksize=4)
    counts = {}
    mind = None
    for r in res:
        for c, a, b, d in r:
            counts[c] = counts.get(c, 0) + 1
            if c == "EXACT": print("EXACT", a, b)
            elif c == "EQUAL_OTHER": print("EQUAL_OTHER", a, b, d)
            else:
                dv = float(d); mind = dv if mind is None or dv < mind else mind
    print("groups", len(groups), "pairs", counts, "min_unequal_diff", mind)
