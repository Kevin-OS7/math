#!/usr/bin/env python3
"""Numerical checks of Conjecture 25 of Liu, Li, Guo and Song (arXiv:1712.06842, Sect. 5.2).

Part 1. For q in {2,4,8,16}, r in {2,3,4}, t in {1,2,3}, m = 2^r t + 2^(r-1), n = q^m + 1:
  * decide whether the conjectured delta_1, delta_2, delta_3 are q-cyclotomic coset leaders mod n;
  * if n < 10^12, find the three largest coset leaders by scanning downwards from delta_1
    (the largest leader by Theorem 24 of the paper), giving up after 10^6 candidates;
  * if n < 10^8, also confirm that delta_1 is the largest leader by scanning down from floor(n/2)
    (every coset contains both x and n - x because q^m = -1 mod n).
Part 2. For t = 1, check that delta_2 is the second largest leader (delta_1 being the largest by
  Theorem 24) and compare the third largest leader with the corrected formula
  delta_2 - (q-1) q^(2^(r-2)+1) prod_{j=1}^{r-2} (q^(2^j) - 1).
Part 3. The branch m = 2^r (r = 1, 2, 3, 4) of the conjecture, for q in {2,4,8,16}:
  same checks as in Part 1.

Pure Python 3, no dependencies:  python3 conj25_check.py
"""
from math import prod


def phi_prime(x, q):
    # (q/2)(q^(2^x)-1)...(q^(2^0)-1) for x >= 0, and q/2 for x < 0 (empty product)
    return (q // 2) * prod(q ** (2 ** j) - 1 for j in range(x + 1))


def conjectured(q, r, t):
    m = 2 ** r * t + 2 ** (r - 1)
    n = q ** m + 1
    a, rem = divmod(n, q ** (2 ** (r - 1)) + 1)
    assert rem == 0
    d1 = a * phi_prime(r - 2, q)
    num, den = 2 * (d1 + phi_prime(r - 1, q)), q ** (2 ** r)
    assert num % den == 0
    d2 = d1 - num // den
    d3 = d2 - ((q - 1) * q ** 2 if t == 1 else 2 * phi_prime(r - 1, q))
    return m, n, d1, d2, d3


def is_leader(q, n, a):
    b = a * q % n
    while b != a:
        if b < a:
            return False
        b = b * q % n
    return True


def orbit_min(q, n, a):
    best, b = a, a * q % n
    while b != a:
        best = min(best, b)
        b = b * q % n
    return best


def leaders_from(q, n, start, k, limit=None):
    out, a = [], start
    while len(out) < k and a > 0 and (limit is None or start - a < limit):
        if is_leader(q, n, a):
            out.append(a)
        a -= 1
    return out


def part1():
    print("Part 1: Conjecture 25 for q in {2,4,8,16}, r in {2,3,4}, t in {1,2,3}", flush=True)
    for q in (2, 4, 8, 16):
        for r in (2, 3, 4):
            for t in (1, 2, 3):
                m, n, d1, d2, d3 = conjectured(q, r, t)
                flags = [is_leader(q, n, d) for d in (d1, d2, d3)]
                line = f"q={q:2d} r={r} t={t} m={m:2d}: leader(d1,d2,d3)={flags}"
                if not flags[2]:
                    line += f" d3={d3} orbit_min={orbit_min(q, n, d3)}"
                if n < 10 ** 12:
                    top = [d1] + leaders_from(q, n, d1 - 1, 2, 10 ** 6)
                    if len(top) == 3:
                        line += f" top3={top} d2_ok={top[1] == d2} d3_ok={top[2] == d3}"
                    else:
                        line += " top3=not found within 10^6 candidates"
                if n < 10 ** 8:
                    line += f" d1_is_max={leaders_from(q, n, n // 2, 1) == [d1]}"
                print(line, flush=True)


def part2():
    print("Part 2: corrected formula for t = 1", flush=True)
    for q, r in [(2, 2), (4, 2), (8, 2), (16, 2), (2, 3), (4, 3), (8, 3), (16, 3),
                 (2, 4), (4, 4), (2, 5), (8, 4)]:
        m, n, d1, d2, d3 = conjectured(q, r, 1)
        gap = (q - 1) * q ** (2 ** (r - 2) + 1) * prod(q ** (2 ** j) - 1 for j in range(1, r - 1))
        pred = d2 - gap
        if gap > 3 * 10 ** 7:
            print(f"q={q:2d} r={r} m={m}: gap {gap} too large to scan; "
                  f"predicted value is a leader: {is_leader(q, n, pred)}", flush=True)
            continue
        # delta_2 must be the second largest leader: no leader strictly between delta_2 and delta_1
        second_ok = is_leader(q, n, d2) and not leaders_from(q, n, d1 - 1, 1, d1 - d2 - 1)
        third = leaders_from(q, n, d2 - 1, 1)[0]
        print(f"q={q:2d} r={r} m={m}: delta_2 is second largest: {second_ok}; third largest leader {third}, "
              f"predicted {pred}, match={third == pred}", flush=True)


def conjectured_power(q, r):
    m = 2 ** r
    if m == 2:
        d1 = q * (q - 1) // 2
        d2 = d1 - (q - 1)
        return m, q ** m + 1, d1, d2, d2 - 1
    d1 = phi_prime(r - 1, q)
    d2 = d1 - 2 * phi_prime(r - 3, q)
    d3 = d1 - (q - 1) * (q ** 2 - 1) if m == 4 else d1 - 2 * q ** (2 ** (r - 2)) * phi_prime(r - 4, q)
    return m, q ** m + 1, d1, d2, d3


def part3():
    print("Part 3: the branch m = 2^r", flush=True)
    for q in (2, 4, 8, 16):
        for r in (1, 2, 3, 4):
            m, n, d1, d2, d3 = conjectured_power(q, r)
            if not all(0 < d < n for d in (d1, d2, d3)):
                print(f"q={q:2d} m={m:2d}: formulas give ({d1},{d2},{d3}); skipped", flush=True)
                continue
            flags = [is_leader(q, n, d) for d in (d1, d2, d3)]
            line = f"q={q:2d} m={m:2d}: leader(d1,d2,d3)={flags}"
            if n < 10 ** 12:
                top = [d1] + leaders_from(q, n, d1 - 1, 2, 10 ** 6)
                if len(top) == 3:
                    line += f" top3={top} d2_ok={top[1] == d2} d3_ok={top[2] == d3}"
                else:
                    line += " top3=not found within 10^6 candidates"
            if n < 10 ** 8:
                line += f" d1_is_max={leaders_from(q, n, n // 2, 1) == [d1]}"
            print(line, flush=True)


if __name__ == "__main__":
    part1()
    part2()
    part3()
