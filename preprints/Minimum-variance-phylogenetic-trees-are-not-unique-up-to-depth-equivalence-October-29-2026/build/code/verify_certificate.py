#!/usr/bin/env python3
"""Exact finite certificate for the independent global-minimality proof."""
N = 67_256_579
C = 4913

def entry(k, i):
    r = (1 << k) - N
    b = (r - C) // 32 + i
    L = [t + 5 for t in range(b.bit_length()) if (b >> t) & 1]
    a = 32 * b - len(L)
    q = sum(t*t for t in L)
    e = sum(L)
    if a <= r:
        q += r-a
        e += r-a
    else:
        q += 2*(a-r)
        e -= 2*(a-r)
    return b, L, q, e

hits = []
for k in range(27, 97):
    for i in range(240):
        b, L, q, e = entry(k, i)
        if q <= C:
            assert k == 27 and q == C and e*e == 279*279
            hits.append((k, i, b, L, q, e))
assert len(hits) == 2
print('Verified 16800 entries using exact integers.')
for hit in hits:
    print(hit)

A = {27-t: 1 for t in hits[0][3]}
A.update({26: 13, 27: N-29})
B = {27-t: 1 for t in hits[1][3]}
B.update({27: N-507, 28: 496})
for name, profile in [('A', A), ('B', B)]:
    assert sum(profile.values()) == N
    h = max(profile)
    assert sum(c*(1 << (h-d)) for d,c in profile.items()) == 1 << h
    S = sum(c*d for d,c in profile.items())
    Q = sum(c*d*d for d,c in profile.items())
    D = N*Q-S*S
    assert D == 330_431_494_786
    print(name, 'profile=', sorted(profile.items()), 'S=', S, 'Q=', Q, 'D=', D)
assert A != B
