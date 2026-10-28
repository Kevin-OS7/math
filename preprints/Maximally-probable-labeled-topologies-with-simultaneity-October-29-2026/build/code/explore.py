#!/usr/bin/env python3
"""Exact arithmetic tests for the Dickey--Rosenberg split inequalities.

One CPU core; all coefficients are Python integers. No floating point.
"""
from argparse import ArgumentParser
from math import comb
from time import monotonic
import json


def split(n):
    """The paper's power-of-two split, without real logarithms."""
    assert n >= 2
    t = 1
    while 3*t < n:
        t *= 2
    assert t < n <= 3*t
    return t, n-t


def greedy_omega(N, M):
    g = [None, [1]*(M+1)]
    for n in range(2, N+1):
        a, b = split(n)
        row = [0]
        for j in range(M):
            row.append(row[-1] + g[a][j]*g[b][j])
        g.append(row)
    return g


def binomial_coefficients(values):
    """Newton coefficients Δ^r p(0), with p known on 0,...,degree."""
    row = list(values)
    out = []
    while row:
        out.append(row[0])
        row = [b-a for a,b in zip(row,row[1:])]
    return out


def omega_from_events(events, M):
    return [sum(e*comb(m,z) for z,e in enumerate(events) if z <= m)
            for m in range(M+1)]


def event_merge(left, right):
    """Independent positive-coefficient recursion, including empty subtrees."""
    out = [0]*(len(left)+len(right))
    for a, ea in enumerate(left):
        for b, eb in enumerate(right):
            for overlap in range(min(a,b)+1):
                k = a+b-overlap
                out[k+1] += ea*eb*comb(k,overlap)*comb(k-overlap,a-overlap)
    return out


def check_split(N, M, coefficientwise=False):
    if coefficientwise:
        M = max(M, N-2)
    g = greedy_omega(N,M)
    count = 0
    equal = []
    t0 = monotonic()
    for n in range(2,N+1):
        t, u = split(n)
        best = [x*y for x,y in zip(g[t],g[u])]
        for a in range(1,n//2+1):
            b = n-a
            if sorted((a,b)) == sorted((t,u)):
                continue
            diff = [v-x*y for v,x,y in zip(best,g[a],g[b])]
            if min(diff) < 0:
                j = next(j for j,x in enumerate(diff) if x < 0)
                return dict(ok=False,kind='pointwise',n=n,a=a,j=j,diff=diff[j])
            if coefficientwise:
                cs = binomial_coefficients(diff[:n-1])
                if min(cs) < 0:
                    z = next(z+1 for z,x in enumerate(cs) if x < 0)
                    return dict(ok=False,kind='coefficient',n=n,a=a,z=z,diff=cs[z-1])
                if not any(cs): equal.append((n,a))
            count += 1
        if n%32 == 0:
            print(json.dumps(dict(progress=n,seconds=monotonic()-t0)),flush=True)
    # Independent validation of the finite-difference method on modest cases.
    for n in range(2,min(N,32)+1):
        a,b=split(n)
        e = event_merge(binomial_coefficients(g[a][:a]),
                        binomial_coefficients(g[b][:b]))
        assert e == binomial_coefficients(g[n][:n])
    return dict(ok=True,N=N,M=M,coefficientwise=coefficientwise,
                nontrivial_splits=count,equal_polynomials=equal,
                seconds=monotonic()-t0)


if __name__ == '__main__':
    p=ArgumentParser()
    p.add_argument('--N',type=int,default=128)
    p.add_argument('--M',type=int,default=128)
    p.add_argument('--coefficients',action='store_true')
    p.add_argument('--output')
    args=p.parse_args()
    result=check_split(args.N,args.M,args.coefficients)
    print(json.dumps(result),flush=True)
    if args.output:
        with open(args.output,'w') as f: json.dump(result,f,indent=2)
