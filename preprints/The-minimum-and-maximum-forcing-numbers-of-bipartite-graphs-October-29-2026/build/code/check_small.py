#!/usr/bin/env python3
"""Exact checks; standard library only. Run: nice -n 10 python3 check_small.py."""
from itertools import permutations, combinations
from random import Random
import json


def perfect_matchings(rows):
    n = len(rows)
    return [p for p in permutations(range(n))
            if all(rows[i] >> p[i] & 1 for i in range(n))]


def forcing_set(p, matchings):
    n = len(p)
    for s in range(n + 1):
        for fixed in combinations(range(n), s):
            if all(q == p or any(p[i] != q[i] for i in fixed)
                   for q in matchings):
                return set(fixed)
    raise AssertionError("the whole matching must force")


def check(rows):
    n = len(rows)
    matchings = perfect_matchings(rows)
    fs = [forcing_set(p, matchings) for p in matchings]
    f = min(map(len, fs))
    F = max(map(len, fs))
    assert n <= (f + 1) * (n - F), (rows, f, F)
    idx = next(i for i, s in enumerate(fs) if len(s) == f)
    base, fixed = matchings[idx], fs[idx]
    inv = {b: a for a, b in enumerate(base)}
    remaining = set(range(n)) - fixed
    order = []
    while remaining:
        sources = [j for j in remaining if not any(
            i != j and rows[i] >> base[j] & 1 for i in remaining)]
        assert sources, "unique residual matching must have an acyclic digraph"
        j = min(sources)
        order.append(j)
        remaining.remove(j)
    rank = {a: i + 1 for i, a in enumerate(order)}
    m = len(order)
    for p in matchings:
        intervals = [(rank.get(a, 0), rank.get(inv[b], m + 1))
                     for a, b in enumerate(p)]
        assert all(l <= r for l, r in intervals)
        for t in range(m + 2):
            overlap = sum(l <= t <= r for l, r in intervals)
            assert overlap == (f + 1 if 1 <= t <= m else f)
        remaining = set(range(n))
        chosen = []
        while remaining:
            e = min(remaining, key=lambda i: (intervals[i][1], i))
            r = intervals[e][1]
            removed = {i for i in remaining if intervals[i][0] <= r}
            assert len(removed) <= f + 1
            chosen.append(e)
            remaining -= removed
        assert n <= (f + 1) * len(chosen)
        fixed_p = set(range(n)) - set(chosen)
        assert all(q == p or any(q[i] != p[i] for i in fixed_p)
                   for q in matchings)
    return f, F


def main():
    summary = []
    for n in range(1, 5):
        off_diag = [(i, j) for i in range(n) for j in range(n) if i != j]
        pairs = set()
        for mask in range(1 << len(off_diag)):
            rows = [1 << i for i in range(n)]
            for bit, (i, j) in enumerate(off_diag):
                if mask >> bit & 1:
                    rows[i] |= 1 << j
            pairs.add(check(rows))
        summary.append(dict(n=n, graphs=1 << len(off_diag),
                            spectrum_pairs=sorted(pairs), mode="exhaustive, diagonal present"))
        print(json.dumps(summary[-1]), flush=True)
    rng = Random(20261029)
    for n, count in [(5, 150), (6, 50), (7, 12), (8, 3)]:
        for _ in range(count):
            density = rng.uniform(0.1, 0.7)
            rows = [sum(1 << j for j in range(n)
                        if i == j or rng.random() < density) for i in range(n)]
            check(rows)
        summary.append(dict(n=n, graphs=count, mode="seeded random"))
        print(json.dumps(summary[-1]), flush=True)
    with open("computation_results.json", "w") as out:
        json.dump(summary, out, indent=2)


if __name__ == "__main__":
    main()
