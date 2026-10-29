#!/usr/bin/env python3
"""Check the formula e(G) = 2 n |s| for connected strongly regular graphs with eigenvalues
k > r >= 0 > s (multiplicities 1, f, g) satisfying  r s + k (f s + g r) >= 0, and the resulting
non-cospectral pairs  T(n) = L(K_n)  vs  L_2(m) = K_m x K_m  with  n(n-1)/2 = m^2."""
import numpy as np, networkx as nx, math

def e_local(G):
    A = nx.to_numpy_array(G); n = len(A)
    E = np.abs(np.linalg.eigvalsh(A)).sum()
    return sum(E - np.abs(np.linalg.eigvalsh(np.delete(np.delete(A, v, 0), v, 1))).sum() for v in range(n))

def srg_data(G):
    ev = np.linalg.eigvalsh(nx.to_numpy_array(G))
    vals, cnt = np.unique(np.round(ev, 8), return_counts=True)
    assert len(vals) == 3, vals
    s, r, k = vals; g, f, _ = cnt
    return k, r, s, f, g

def check(name, G):
    n = G.number_of_nodes()
    k, r, s, f, g = srg_data(G)
    crit = r * s + k * (f * s + g * r)
    e = e_local(G)
    print(f"{name:16s} n={n:3d} k={k:g} r={r:g} s={s:g} f={f} g={g}  rs+k(fs+gr)={crit:g}  e={e:.6f}  2n|s|={2*n*abs(s):g}")

check("L2(4)=rook", nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(4)))
check("T(6)", nx.line_graph(nx.complete_graph(6)))
check("T(8)", nx.line_graph(nx.complete_graph(8)))
check("T(9)", nx.line_graph(nx.complete_graph(9)))
check("L2(6)", nx.cartesian_product(nx.complete_graph(6), nx.complete_graph(6)))
check("L2(5)", nx.cartesian_product(nx.complete_graph(5), nx.complete_graph(5)))
check("L2(3)", nx.cartesian_product(nx.complete_graph(3), nx.complete_graph(3)))
check("T(5)", nx.line_graph(nx.complete_graph(5)))
check("Petersen", nx.petersen_graph())
# triangular square numbers: n(n-1)/2 = m^2
sols = [(n, math.isqrt(n * (n - 1) // 2)) for n in range(2, 400) if math.isqrt(n * (n - 1) // 2) ** 2 == n * (n - 1) // 2]
print("n(n-1)/2 = m^2 solutions (n, m):", sols)
