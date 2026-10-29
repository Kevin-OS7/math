#!/usr/bin/env python3
"""Find connection sets C in Z_4^2 with Cay(Z_4^2, C) strongly regular (16,10,6,6),
i.e. isomorphic to the complement of the Clebsch graph (the unique SRG(16,5,0,2) is Clebsch)."""
import itertools
import numpy as np
V = [(a, b) for a in range(4) for b in range(4)]
nz = [v for v in V if v != (0, 0)]
neg = lambda v: ((-v[0]) % 4, (-v[1]) % 4)
classes = []
for v in nz:
    c = frozenset({v, neg(v)})
    if c not in classes: classes.append(c)
found = []
for r in range(len(classes) + 1):
    for sub in itertools.combinations(classes, r):
        C = set().union(*sub) if sub else set()
        if len(C) != 10: continue
        A = np.array([[1 if ((x[0]-y[0]) % 4, (x[1]-y[1]) % 4) in C else 0 for y in V] for x in V])
        J = np.ones((16, 16), dtype=int); I = np.eye(16, dtype=int)
        if (A @ A == 10 * I + 6 * A + 6 * (J - I - A)).all():
            found.append(sorted(C))
print(len(found), "connection sets giving SRG(16,10,6,6)")
for C in found[:5]: print(C)
