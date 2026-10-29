#!/usr/bin/env python3
"""Exact comparison of graphs grouped by (numerically) equal local energy.
For each group, key(G) = (charpoly(A_G), sorted multiset of charpoly(A_{G-v})).
Equal keys imply exactly equal local energy.  Groups whose keys differ are re-evaluated with
50-digit arithmetic (hp_check.local_energy)."""
import sys, re, ast
from hp_check import g6_adj, local_energy
import mpmath as mp

def charpoly(A):
    # Faddeev-LeVerrier with exact integers: returns coefficients c_0..c_n of det(xI - A)
    n = len(A)
    if n == 0: return (1,)
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    M = [[0] * n for _ in range(n)]
    c = [0] * (n + 1); c[n] = 1
    for k in range(1, n + 1):
        # M_k = A M_{k-1} + c_{n-k+1} I
        AM = [[sum(A[i][l] * M[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        M = [[AM[i][j] + c[n - k + 1] * I[i][j] for j in range(n)] for i in range(n)]
        AM = [[sum(A[i][l] * M[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        tr = sum(AM[i][i] for i in range(n))
        assert tr % k == 0
        c[n - k] = -tr // k
    return tuple(c)

def key(g):
    A = g6_adj(g); n = len(A)
    dels = sorted(charpoly([[A[i][j] for j in range(n) if j != v] for i in range(n) if i != v]) for v in range(n))
    return (charpoly(A), tuple(dels))

def main():
    groups = []
    for line in open(sys.argv[1]):
        m = re.match(r'\s+e=(\S+) spread=(\S+) (\[.*\])', line)
        if m:
            groups.append((float(m.group(2)), [g for g, _ in ast.literal_eval(m.group(3))]))
    same_key, other = [], []
    for sp, gs in groups:
        ks = [key(g) for g in gs]
        if all(k == ks[0] for k in ks):
            same_key.append((sp, gs))
        else:
            other.append((sp, gs, ks))
    print(f"groups={len(groups)} identical_vertex_deleted_polys={len(same_key)} other={len(other)}")
    for sp, gs in same_key:
        print("EXACT", sp, gs)
    mp.mp.dps = 50
    for sp, gs, ks in other:
        if sp < 1e-12:
            vals = [local_energy(g6_adj(g)) for g in gs]
            print("HP", sp, gs, mp.nstr(max(vals) - min(vals), 5),
                  "cospectral" if all(k[0] == ks[0][0] for k in ks) else "not cospectral")

if __name__ == "__main__":
    main()
