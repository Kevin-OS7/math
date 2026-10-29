/* For every n in [lo, hi], minimize D = n*Q - S^2 (= n^2 V) over the candidate family of
   Theorem 2 of Coronado-Mir-Rossello-Rotger (2020): trees with leaves at depths h, h-1 and one
   leaf at each depth h-l, l in L, 5 <= l <= h-2, L a set (h = floor(log2 n) .. +2).
   Exact 128-bit integer arithmetic.  Reports every n whose minimum is attained by >= 2
   distinct depth profiles.  Usage: minvar_scan lo hi   (OpenMP over n) */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

static int scan(uint64_t n, __int128 *bestOut) {
    int m = 63 - __builtin_clzll(n);
    __int128 best = ((__int128)1) << 126;
    int ties = 0;
    for (int h = m; h <= m + 2; h++) {
        int k = h - 6;
        if (k < 0) k = 0;
        int64_t a = 0, s = 0, q = 0, j = 0;
        uint64_t prev = 0;
        for (uint64_t i = 0; i < (1ULL << k); i++) {
            uint64_t gray = i ^ (i >> 1);
            if (i) {
                int bit = __builtin_ctzll(gray ^ prev), l = bit + 5;
                int sg = (gray & (1ULL << bit)) ? 1 : -1;
                a += sg * ((1LL << l) - 1); s += sg * l; q += sg * l * l; j += sg;
            }
            prev = gray;
            int64_t p1 = (1LL << h) - (int64_t)n - a, p0 = (int64_t)n - p1 - j;
            if (p1 < 0 || p0 <= 0) continue;
            int64_t P = p1 + s, Q = p1 + q;
            __int128 D = (__int128)n * Q - (__int128)P * P;
            if (D < best) { best = D; ties = 1; }
            else if (D == best) ties++;
        }
    }
    *bestOut = best;
    return ties;
}

int main(int argc, char **argv) {
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    uint64_t found = 0;
    #pragma omp parallel for schedule(dynamic, 64) reduction(+:found)
    for (uint64_t n = lo; n <= hi; n++) {
        __int128 best;
        int t = scan(n, &best);
        if (t >= 2) {
            found++;
            #pragma omp critical
            { printf("TIE n=%" PRIu64 " ties=%d D=%" PRIu64 "\n", n, t, (uint64_t)best); fflush(stdout); }
        }
    }
    printf("DONE lo=%" PRIu64 " hi=%" PRIu64 " tie_count=%" PRIu64 "\n", lo, hi, found);
    return 0;
}
