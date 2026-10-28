#!/usr/bin/env python3
"""Exhaustively audit the switching injection on a seven-vertex ambient tree.

Includes every pair of admissible zero-extended maps into {0,1,2,3,4}.
No randomness or floating point is used.
"""
from itertools import product
from collections import Counter


def all_maps(height, bound):
    if height == 0:
        return [()]
    out=[(0,)*((1<<height)-1)]
    for root in range(1,bound+1):
        for a,b in product(all_maps(height-1,root-1), repeat=2):
            # Breadth-first order: root then corresponding levels of children.
            row=[root]
            for d in range(height-1):
                start=(1<<d)-1
                stop=(1<<(d+1))-1
                row.extend(a[start:stop]); row.extend(b[start:stop])
            out.append(tuple(row))
    return out


def admissible(f):
    return all(f[v-1] == 0 or f[v-1] < f[v//2-1] for v in range(2,len(f)+1))


def switch(f,g,mark):
    lo=[min(x,y) for x,y in zip(f,g)]
    hi=[max(x,y) for x,y in zip(f,g)]
    adj=[[] for _ in f]
    for v in range(2,len(f)+1):
        u=v//2
        if hi[v-1]>0 and lo[u-1]<=hi[v-1]:
            assert lo[u-1]<hi[u-1] and lo[v-1]<hi[v-1]
            adj[u-1].append(v-1); adj[v-1].append(u-1)
    affected=set(mark)
    queue=list(mark)
    while queue:
        v=queue.pop()
        for u in adj[v]:
            if u not in affected:
                affected.add(u); queue.append(u)
    return (tuple(g[v] if v in affected else f[v] for v in range(len(f))),
            tuple(f[v] if v in affected else g[v] for v in range(len(f))))


def main():
    maps=all_maps(3,4)
    assert len(maps)==len(set(maps))
    assert all(admissible(f) for f in maps)
    count=0
    for f,g in product(maps,repeat=2):
        P={v for v,x in enumerate(f) if x}
        Q={v for v,x in enumerate(g) if x}
        F,H=switch(f,g,Q-P)
        assert admissible(F) and admissible(H)
        assert {v for v,x in enumerate(F) if x}==P|Q
        assert {v for v,x in enumerate(H) if x}==P&Q
        assert max(F,default=0)<=max(max(f,default=0),max(g,default=0))
        assert max(H,default=0)<=max(g,default=0)
        assert Counter(F+H)==Counter(f+g)
        assert switch(F,H,Q-P)==(f,g)
        count+=1
    print(dict(admissible_maps=len(maps),pairs_checked=count,ok=True))


if __name__=='__main__': main()
