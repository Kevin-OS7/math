/* Fast exact scan of the Theorem-2 family of Coronado-Mir-Rossello-Rotger (2020).
   Candidate (h, b): leaves at depths h (p0 of them), h-1 (p1), and one leaf at depth h-l for
   each l = 5 + (bit position of b), b < 2^(h-6).  With a = sum(2^l - 1) = 32b - j:
   p1 = 2^h - n - a, p0 = n - p1 - j; valid iff p1 >= 0 and p0 > 0.
   D = n*Q - P^2, P = p1 + s, Q = p1 + q (centered at h; s = sum l, q = sum l^2).
   Pruning (exact): let c be an integer nearest to the mean depth.  Then |E_c| <= n/2 and
   |E_c| <= R_c, so D = n*R_c - E_c^2 >= n*R_c/2.  The mean depth is h - (p1 + sum l)/n, and
   sum l <= 5 + ... + (h-2) < m^2 < n/2 for n > 2^20 (for n <= 2^20 the full enumeration agrees),
   so c is h or h-1.  If c = h then R_c >= p1; if c = h-1 then R_c >= p0.  Hence every candidate
   with D <= Dbest has p1 <= Rmax or p0 <= Rmax, Rmax = 2*Dbest/n; this gives two short windows
   of b for each h (the +-1 margins absorb truncating division).  The loop below enlarges Rmax
   until Rmax >= ceil(2*Dbest/n), so the minimum and the number of minimizers are exact.
   Heights: 2^h >= n gives h >= m, and 2^h = p0 + 2 p1 + sum 2^l < 2n + 2^(h-1) gives h <= m+2.
   Usage: minvar_fast lo hi [check]   ("check" compares with the full enumeration). */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

typedef __int128 i128;

static inline int eval(uint64_t n, int h, uint64_t b, i128 *D) {
    int64_t a = 0, s = 0, q = 0, j = 0;
    for (uint64_t x = b; x; x &= x - 1) {
        int l = __builtin_ctzll(x) + 5;
        a += (1LL << l) - 1; s += l; q += (int64_t)l * l; j++;
    }
    int64_t p1 = (1LL << h) - (int64_t)n - a, p0 = (int64_t)n - p1 - j;
    if (p1 < 0 || p0 <= 0) return 0;
    int64_t P = p1 + s, Q = p1 + q;
    *D = (i128)n * Q - (i128)P * P;
    return 1;
}

/* minimum over the windows for a given Rmax; returns number of distinct minimizers */
static int windows(uint64_t n, int64_t Rmax, i128 *best, int *bh, uint64_t *bb) {
    int m = 63 - __builtin_clzll(n), ties = 0;
    *best = ((i128)1) << 126;
    for (int h = m; h <= m + 2; h++) {
        uint64_t bmax = h >= 6 ? 1ULL << (h - 6) : 1;  /* b < bmax; only L = {} if h < 7 */
        int64_t H = 1LL << h;
        /* window 1: 0 <= p1 <= Rmax, p1 = H - n - 32b + j, 0 <= j <= h-6 */
        int64_t lo1 = (H - (int64_t)n - Rmax) / 32 - 1, hi1 = (H - (int64_t)n + h) / 32 + 1;
        /* window 2: 1 <= p0 <= Rmax, p0 = 2n - H + 32b - 2j */
        int64_t lo2 = (H - 2 * (int64_t)n) / 32 - 1, hi2 = (H - 2 * (int64_t)n + Rmax + 2 * h) / 32 + 1;
        int64_t los[2] = {lo1, lo2}, his[2] = {hi1, hi2}, clo[2], chi[2];
        for (int w = 0; w < 2; w++) {
            int64_t lo = los[w] < 0 ? 0 : los[w], hi = his[w] >= (int64_t)bmax ? (int64_t)bmax - 1 : his[w];
            clo[w] = lo; chi[w] = hi;
            for (int64_t b = lo; b <= hi; b++) {
                if (w == 1 && b >= clo[0] && b <= chi[0]) continue;   /* already seen in window 1 */
                i128 D;
                if (!eval(n, h, (uint64_t)b, &D)) continue;
                if (D < *best) { *best = D; ties = 1; *bh = h; *bb = b; }
                else if (D == *best) ties++;
            }
        }
    }
    return ties;
}

static int full(uint64_t n, i128 *bestOut) {
    int m = 63 - __builtin_clzll(n), ties = 0;
    i128 best = ((i128)1) << 126;
    for (int h = m; h <= m + 2; h++) {
        for (uint64_t b = 0; b < (h >= 6 ? 1ULL << (h - 6) : 1); b++) {
            i128 D;
            if (!eval(n, h, b, &D)) continue;
            if (D < best) { best = D; ties = 1; } else if (D == best) ties++;
        }
    }
    *bestOut = best;
    return ties;
}

int main(int argc, char **argv) {
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int check = argc > 3 && !strcmp(argv[3], "check");
    uint64_t found = 0, mismatch = 0, passes2 = 0;
    #pragma omp parallel for schedule(dynamic, 256) reduction(+:found,mismatch,passes2)
    for (uint64_t n = lo; n <= hi; n++) {
        int64_t Rmax = 64;
        i128 best; int bh = 0; uint64_t bb = 0; int t;
        for (;;) {
            t = windows(n, Rmax, &best, &bh, &bb);
            if (t == 0) { if (Rmax > (1LL << 40)) { printf("NOCAND n=%" PRIu64 "\n", n); break; } Rmax *= 2; continue; }
            i128 need = (2 * best + n - 1) / n;              /* ceil(2 Dbest / n) */
            if (need <= Rmax) break;
            Rmax = (int64_t)need; passes2++;
        }
        if (t >= 2) {
            found++;
            #pragma omp critical
            { printf("TIE n=%" PRIu64 " ties=%d D=%" PRIu64 "\n", n, t, (uint64_t)best); fflush(stdout); }
        }
        if (check) {
            i128 fb; int ft = full(n, &fb);
            if (fb != best || ft != t) {
                mismatch++;
                #pragma omp critical
                { printf("MISMATCH n=%" PRIu64 "\n", n); fflush(stdout); }
            }
        }
    }
    printf("DONE lo=%" PRIu64 " hi=%" PRIu64 " ties=%" PRIu64 " mismatches=%" PRIu64 " repasses=%" PRIu64 "\n",
           lo, hi, found, mismatch, passes2);
    return 0;
}
