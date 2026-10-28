import numpy as np
LIM = 2*10**7
s = np.ones(LIM+1, dtype=bool); s[:2] = False
for i in range(2, int(LIM**0.5)+1):
    if s[i]: s[i*i::i] = False
primes = np.nonzero(s)[0]              # primes[k-1] = p_k
pi = np.cumsum(s)                       # pi[x] = #primes <= x
def rev(n, b):
    r = 0
    while n: r = r*b + n % b; n //= b
    return r
def ndig(n, b):
    d = 0
    while n: d += 1; n //= b
    return d
for b in range(2, 17):
    # cycles must live in a digit-length d with pi(b^d - 1) >= b^(d-1); find all such d with b^d <= LIM
    ds = [d for d in range(1, 40) if b**d <= LIM and pi[b**d - 1] >= b**(d-1)]
    dmax_checked = max(d for d in range(1,40) if b**d <= LIM)
    # sanity: for the first d beyond ds, the density inequality fails and keeps failing (we only check up to LIM)
    K = int(pi[b**max(ds) - 1]) if ds else 0
    f = {k: rev(int(primes[k-1]), b) for k in range(1, K+1)}
    cycles = set()
    for k0 in range(1, K+1):
        seen = []; k = k0
        while 1 <= k <= K and k not in seen:
            seen.append(k); k = f[k]
        if 1 <= k <= K and k in seen:
            c = seen[seen.index(k):]; m = c.index(min(c)); cycles.add(tuple(c[m:] + c[:m]))
    print(f"base {b:2d}: possible cycle digit-lengths {ds} (checked d<= {dmax_checked}); cycles: {sorted(cycles)}")
# base 10 check of the key inequality
for d in range(1, 8): print(d, int(pi[10**d - 1]), 10**(d-1), int(pi[10**d-1]) < 10**(d-1))
