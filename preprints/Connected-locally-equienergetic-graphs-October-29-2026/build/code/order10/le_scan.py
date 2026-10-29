#!/usr/bin/env python3
"""Exhaustive search for locally equienergetic pairs of connected graphs of order n.

Local energy e(G) = sum_v (E(G) - E(G - v)) = n E(G) - sum_v E(G - v), where E is the sum of
absolute values of adjacency eigenvalues.  For each n, all connected graphs (nauty geng -c,
one per isomorphism class) are evaluated in double precision; values agreeing to 1e-8 are
grouped and reported for exact verification.

usage: le_scan.py GENG n [workers]
"""
import subprocess, sys, numpy as np
from multiprocessing import Pool

def parse_g6(lines, n):
    """graph6 lines (bytes, equal length) -> (N, n, n) float64 adjacency matrices."""
    N = len(lines)
    raw = np.frombuffer(b"".join(lines), dtype=np.uint8).reshape(N, -1)[:, 1:].astype(np.int64) - 63
    bits = ((raw[:, :, None] >> np.arange(5, -1, -1)) & 1).reshape(N, -1)
    A = np.zeros((N, n, n))
    k = 0
    for j in range(1, n):
        for i in range(j):
            A[:, i, j] = A[:, j, i] = bits[:, k]
            k += 1
    return A

def energies(A):
    return np.abs(np.linalg.eigvalsh(A)).sum(axis=1)

def local_energy(args):
    lines, n = args
    A = parse_g6(lines, n)
    E = energies(A)
    tot = np.zeros(len(lines))
    for v in range(n):
        keep = [u for u in range(n) if u != v]
        tot += energies(A[:, keep][:, :, keep])
    return n * E - tot, E

def main():
    geng, n = sys.argv[1], int(sys.argv[2])
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    out = subprocess.run([geng, "-c", "-q", str(n)], capture_output=True, check=True).stdout
    lines = out.split(b"\n")[:-1]
    chunk = 20000
    jobs = [(lines[i:i + chunk], n) for i in range(0, len(lines), chunk)]
    with Pool(workers) as pool:
        res = pool.map(local_energy, jobs)
    e = np.concatenate([r[0] for r in res]); E = np.concatenate([r[1] for r in res])
    order = np.argsort(e)
    es = e[order]
    tol = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-8
    close = np.nonzero(np.diff(es) < tol)[0]
    groups, cur = [], None
    for i in close:
        if cur is not None and cur[-1] == i:
            cur.append(i + 1)
        else:
            cur = [i, i + 1]; groups.append(cur)
    print(f"n={n} graphs={len(lines)} groups={len(groups)}", flush=True)
    for g in groups:
        idx = order[g]
        print("  e=%.12f spread=%.3e" % (e[idx[0]], e[idx[-1]] - e[idx[0]]), [(lines[j].decode(), round(float(E[j]), 10)) for j in idx], flush=True)

if __name__ == "__main__":
    main()
