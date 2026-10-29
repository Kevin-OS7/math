#!/usr/bin/env python3
"""Analyse an order-10 locally equienergetic pair (graph6 input): deck matching, isomorphic decks,
Godsil-McKay switching sets, and simple distinguishing invariants."""
import sys, itertools
import networkx as nx
import sympy as sp

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

x = sp.symbols('x')
def cp(G, nodes=None):
    nodes = sorted(G.nodes()) if nodes is None else nodes
    A = sp.Matrix(len(nodes), len(nodes), lambda i, j: 1 if G.has_edge(nodes[i], nodes[j]) else 0)
    return sp.expand(A.charpoly(x).as_expr())

def analyse(sG, sH, verbose=True):
    G, H = g6(sG), g6(sH)
    n = G.number_of_nodes()
    out = {}
    out['edgesG'] = sorted(G.edges()); out['edgesH'] = sorted(H.edges())
    assert cp(G) == cp(H)
    dG = {v: cp(G.subgraph([u for u in G if u != v])) for v in G}
    dH = {w: cp(H.subgraph([u for u in H if u != w])) for w in H}
    match = {v: [w for w in H if dH[w] == dG[v]] for v in G}
    iso = {v: [w for w in match[v] if nx.is_isomorphic(G.subgraph([u for u in G if u != v]), H.subgraph([u for u in H if u != w]))] for v in G}
    out['match'] = match; out['iso'] = iso
    # GM switching sets C (even size 2..n-2) in G whose switching gives a graph isomorphic to H
    gm = []
    for k in (2, 4, 6, 8):
        for C in itertools.combinations(range(n), k):
            sub = G.subgraph(C)
            if len({d for _, d in sub.degree()}) != 1: continue
            ok = True
            for u in range(n):
                if u in C: continue
                t = sum(1 for c in C if G.has_edge(u, c))
                if t not in (0, k // 2, k): ok = False; break
            if not ok: continue
            G2 = G.copy()
            for u in range(n):
                if u in C: continue
                if sum(1 for c in C if G.has_edge(u, c)) == k // 2:
                    for c in C:
                        if G.has_edge(u, c): G2.remove_edge(u, c)
                        else: G2.add_edge(u, c)
            if nx.is_isomorphic(G2, H):
                gm.append(C)
    out['gm'] = gm
    out['degG'] = sorted(d for _, d in G.degree()); out['degH'] = sorted(d for _, d in H.degree())
    out['conn'] = (nx.is_connected(G), nx.is_connected(H))
    out['diam'] = (nx.diameter(G), nx.diameter(H))
    out['clique'] = (max(len(c) for c in nx.find_cliques(G)), max(len(c) for c in nx.find_cliques(H)))
    out['indep'] = (max(len(c) for c in nx.find_cliques(nx.complement(G))), max(len(c) for c in nx.find_cliques(nx.complement(H))))
    out['girth'] = (nx.girth(G), nx.girth(H))
    out['tri'] = (sum(nx.triangles(G).values()) // 3, sum(nx.triangles(H).values()) // 3)
    # induced 4-vertex subgraph type counts (by edge count + degree sequence)
    def ind4(Gr):
        cnt = {}
        for S in itertools.combinations(range(n), 4):
            sub = Gr.subgraph(S)
            key = tuple(sorted(d for _, d in sub.degree()))
            cnt[key] = cnt.get(key, 0) + 1
        return cnt
    out['ind4'] = (ind4(G), ind4(H))
    # edge "degree pair" multisets
    out['degpairs'] = (sorted(tuple(sorted((G.degree(a), G.degree(b)))) for a, b in G.edges()),
                       sorted(tuple(sorted((H.degree(a), H.degree(b)))) for a, b in H.edges()))
    return out

if __name__ == "__main__":
    sG, sH = sys.argv[1], sys.argv[2]
    o = analyse(sG, sH)
    for k, v in o.items():
        print(k, ':', v)
