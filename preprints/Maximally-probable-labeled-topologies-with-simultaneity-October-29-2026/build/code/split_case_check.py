#!/usr/bin/env python3
"""Audit all dyadic case bounds and all canonical decompositions in Lemma 5."""
from explore import split


def canonical_pair(n):
    return tuple(sorted(split(n)))


def block(q,a,d,n):
    assert q & (q-1) == 0 and q > 0
    assert q <= a <= 2*q and q <= d <= 2*q and a+d <= n
    L=min(2*q,a+d-q)
    S=max(q,a+d-2*q)
    assert L+S == a+d and 1 <= L < n and 1 <= S < n
    return L,S


def check(n,a):
    b=n-a
    assert 1 <= a <= b
    p=1 << (n.bit_length()-2)
    assert 2*p <= n < 4*p
    desired=canonical_pair(n)
    if p <= a and b <= 2*p:
        L,S=block(p,a,b,n)
        assert tuple(sorted((L,S)))==desired
        return 'A'
    if a < p and b > 2*p:
        if b <= 3*p:
            c,d=p,b-p
            assert canonical_pair(b)==tuple(sorted((c,d))) and a <= d
            assert a+c < n
            L,S=block(p,d,a+c,n)
            assert tuple(sorted((L,S)))==desired
            return 'B1'
        c,d=b-2*p,2*p
        assert canonical_pair(b)==tuple(sorted((c,d))) and a <= d
        assert 1 <= a+c < n
        assert tuple(sorted((d,a+c)))==desired
        return 'B2'
    if a < p and b <= 2*p:
        assert p >= 2 and p%2==0 and b > p and n < 3*p
        q=p//2
        if b >= 3*q:
            c,d=b-p,p
            assert canonical_pair(b)==tuple(sorted((c,d))) and a <= d
            assert 1 <= a+c < n
            assert tuple(sorted((d,a+c)))==desired
            return 'C1'
        d=b-q
        assert canonical_pair(b)==tuple(sorted((q,d)))
        L,c=block(q,a,d,n)
        assert L==p and c==n-3*q and c >= q
        assert q+c==n-p and q+c < n
        assert tuple(sorted((p,q+c)))==desired
        return 'C2'
    assert a >= p and 2*p < b < 3*p
    d=b-p
    assert canonical_pair(b)==tuple(sorted((p,d)))
    L,S=block(p,a,d,n)
    assert L==n-2*p and S==p
    assert tuple(sorted((L,2*p)))==desired
    return 'D'


if __name__=='__main__':
    from collections import Counter
    count=Counter(check(n,a) for n in range(2,2049) for a in range(1,n//2+1))
    print(dict(N=2048,pairs=sum(count.values()),cases=dict(count),ok=True))
