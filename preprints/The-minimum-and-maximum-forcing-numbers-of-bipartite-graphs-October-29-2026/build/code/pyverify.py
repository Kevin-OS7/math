# Independent pure-Python check by the definition (no FVS trick): f(G,M) = min |S|, S subset of M,
# such that no other perfect matching contains S.
import sys, itertools
def fF(rows):
    n = len(rows)
    pms = [p for p in itertools.permutations(range(n)) if all(rows[i] >> p[i] & 1 for i in range(n))]
    vals = []
    for p in pms:
        diffs = {sum(1 << i for i in range(n) if q[i] != p[i]) for q in pms if q != p}
        best = None
        for s in range(n + 1):
            for S in itertools.combinations(range(n), s):
                m = sum(1 << i for i in S)
                if all(d & m for d in diffs):
                    best = s; break
            if best is not None: break
        vals.append(best)
    return min(vals), max(vals), len(pms)
n = int(sys.argv[1]); rows = [int(x, 16) for x in sys.argv[2:]]
f, F, npm = fF(rows)
print(f"python-def: n={n} f={f} F={F} pms={npm} (f+1)(n-F)={(f+1)*(n-F)} bound_F={n - -(-n//(f+1))}")
