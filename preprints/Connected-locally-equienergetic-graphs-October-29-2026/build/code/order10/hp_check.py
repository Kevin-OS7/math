#!/usr/bin/env python3
"""High-precision local energies of graphs given in graph6 (mpmath, 50 digits)."""
import sys, mpmath as mp
mp.mp.dps = 50
def g6_adj(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - b)) & 1 for b in range(6)]
    A = [[0] * n for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            A[i][j] = A[j][i] = bits[k]; k += 1
    return A
def energy(A):
    if len(A) == 0: return mp.mpf(0)
    M = mp.matrix(A)
    ev = mp.eigsy(M, eigvals_only=True)
    return sum(abs(x) for x in ev)
def local_energy(A):
    n = len(A)
    E = energy(A)
    tot = mp.mpf(0)
    for v in range(n):
        B = [[A[i][j] for j in range(n) if j != v] for i in range(n) if i != v]
        tot += energy(B)
    return n * E - tot
if __name__ == "__main__":
    for line in sys.stdin:
        gs = line.split()
        vals = [local_energy(g6_adj(g)) for g in gs]
        print(gs, mp.nstr(vals[0], 30), "max diff", mp.nstr(max(vals) - min(vals), 5), flush=True)
