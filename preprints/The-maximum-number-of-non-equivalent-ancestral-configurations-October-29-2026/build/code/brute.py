# Shapes: canonical nested tuples; leaf = ()
import sys
from functools import lru_cache
sys.setrecursionlimit(10000)
def node(x, y):
    return (x, y) if x <= y else (y, x)   # canonical (tuples compare lexicographically)
LEAF = ()
def f(n):
    m, r = divmod(n, 3)
    return (3**m * (2*r*r + 8*r + 23)) // 27
# all shapes with n leaves
shapes = {1: [LEAF]}
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
for n in range(2, NMAX+1):
    s = set()
    for a in range(1, n//2+1):
        b = n - a
        for x in shapes[a]:
            for y in shapes[b]:
                s.add(node(x, y))
    shapes[n] = sorted(s)
P = {LEAF: frozenset([LEAF])}
def prun(t):
    if t in P: return P[t]
    l, r = t
    A, B = prun(l), prun(r)
    res = {LEAF} | {node(x, y) for x in A for y in B}
    k = len(A & B)
    assert len(res) == 1 + len(A)*len(B) - k*(k-1)//2
    P[t] = frozenset(res)
    return P[t]
def size(t):
    return 1 if t == LEAF else size(t[0]) + size(t[1])
out = []
for n in range(2, NMAX+1):
    vals = [(len(prun(t)) - 1, t) for t in shapes[n]]
    M = max(v for v, _ in vals)
    arg = [t for v, t in vals if v == M]
    out.append(M)
    print(n, len(shapes[n]), M, f(n), "OK" if M == f(n) else "MISMATCH", "#maximizers", len(arg), [ (size(t[0]), size(t[1])) for t in arg][:6])
print(out)
