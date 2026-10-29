#!/usr/bin/env python3
"""Brute-force check of the two largest q-cyclotomic coset leaders modulo (q+1)(q^m+1) and
(q+1)(q^m-1) against the formulas of Liu, Wu and Zhu (arXiv:2603.07688, Sect. 6).
Exact integer arithmetic, standard library only:  python3 top_two_check.py"""

def is_leader(q, n, a):
    b = a * q % n
    while b != a:
        if b < a:
            return False
        b = b * q % n
    return True

def top_two(q, n):
    out = []
    a = n - 1
    while len(out) < 2:
        if is_leader(q, n, a):
            out.append(a)
        a -= 1
    return out

def plus_formula(q, m):
    if q % 4 == 1:
        return 3 * (q + 1) * (q ** m + 1) // 4, (3 * q - 1) * (q ** m + 1) // 4
    return (3 * q + 1) * (q ** m + 1) // 4, ((3 * q * q + q - 4) * q ** (m - 1) - (q - 1)) // 4

def minus_formula(q, m):
    d1 = q ** (m + 1) - q ** (m - 1) - q - 1
    if m == 3:
        return d1, (q * q - 1) * q * q - (2 * q + 1)
    return d1, (q * q - 1) * q ** (m - 1) - (q + 1) * (q ** ((m - 1) // 2) + 1)

LIMIT = 4_000_000
bad = 0
print("n = (q+1)(q^m+1), odd q")
for q in range(3, 26, 2):
    for m in (3, 5, 7, 9):
        n = (q + 1) * (q ** m + 1)
        if n > LIMIT:
            continue
        got, want = top_two(q, n), list(plus_formula(q, m))
        bad += got != want
        print(f"  q={q:2d} m={m} n={n}: {got} formula {want} {'OK' if got == want else 'MISMATCH'}", flush=True)
print("n = (q+1)(q^m-1)")
for q in range(2, 26):
    for m in (3, 5, 7, 9, 11):
        n = (q + 1) * (q ** m - 1)
        if n > LIMIT:
            continue
        got, want = top_two(q, n), list(minus_formula(q, m))
        bad += got != want
        print(f"  q={q:2d} m={m} n={n}: {got} formula {want} {'OK' if got == want else 'MISMATCH'}", flush=True)
print("m = 1 (outside the theorems): q = 3")
print("  plus  n=16:", top_two(3, 16), "formula", list(plus_formula(3, 1)))
print("  minus n=8: largest leader", top_two(3, 8)[0], "formula", minus_formula(3, 1)[0])
print("mismatches for m >= 3:", bad)
