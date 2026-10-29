#!/usr/bin/env python3
"""e(T(50)) vs e(L2(35)) on 1225 vertices (both vertex-transitive: e = n (E(G) - E(G - v)))."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
import numpy as np, networkx as nx
def e_vt(G):
    A = nx.to_numpy_array(G); n = len(A)
    return n * (np.abs(np.linalg.eigvalsh(A)).sum() - np.abs(np.linalg.eigvalsh(A[1:, 1:])).sum())
T = nx.line_graph(nx.complete_graph(50)); L = nx.cartesian_product(nx.complete_graph(35), nx.complete_graph(35))
print(T.number_of_nodes(), L.number_of_nodes(), "e(T(50)) =", e_vt(T), " e(L2(35)) =", e_vt(L), " 2n|s| =", 2 * 1225 * 2)
