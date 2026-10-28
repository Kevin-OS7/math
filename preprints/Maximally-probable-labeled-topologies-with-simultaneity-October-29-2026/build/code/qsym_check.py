#!/usr/bin/env python3
"""Test a stronger, multivariate split inequality (one coefficient per label histogram)."""
from collections import defaultdict
from argparse import ArgumentParser
from explore import split
from time import monotonic


def multiply(a,b):
    c=defaultdict(int)
    for x,u in a.items():
        for y,v in b.items():
            c[tuple(i+j for i,j in zip(x,y))]+=u*v
    return c


def check(N,M):
    start=monotonic()
    one={(0,)*M:1}
    g=[None,[one for _ in range(M+1)]]
    for n in range(2,N+1):
        a,b=split(n); row=[{}]
        for j in range(M):
            val=dict(row[-1])
            for c,v in multiply(g[a][j],g[b][j]).items():
                cc=list(c); cc[j]+=1; cc=tuple(cc)
                val[cc]=val.get(cc,0)+v
            row.append(val)
        g.append(row)
    for n in range(2,N+1):
        t,u=split(n); best=multiply(g[t][M],g[u][M])
        for a in range(1,n//2+1):
            b=n-a
            if sorted((a,b))==sorted((t,u)): continue
            for c,v in multiply(g[a][M],g[b][M]).items():
                if v>best.get(c,0):
                    print('FAIL',dict(n=n,a=a,composition=c,greedy=best.get(c,0),other=v),flush=True)
                    return False
        print('PASS',n,'time',monotonic()-start,flush=True)
    return True


if __name__=='__main__':
    p=ArgumentParser()
    p.add_argument('--N',type=int,default=20)
    p.add_argument('--M',type=int,default=5)
    a=p.parse_args()
    print(check(a.N,a.M),flush=True)
