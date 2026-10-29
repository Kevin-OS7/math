// Independent check of  n <= (f(G)+1)(n-F(G))  for bipartite graphs with a perfect matching.
// Graph: A = {0..n-1}, B = {0..n-1}, rows[i] = bitmask of B-neighbours of a_i.  WLOG the
// diagonal {a_i b_i} is a perfect matching (relabel B).
// f(G,M) is computed in two independent ways:
//   (def)  smallest S subset of M such that no other perfect matching contains S  (brute force)
//   (fvs)  minimum feedback vertex set of the digraph D_M (i -> j iff i != j and a_i b_{M(j)} in E)
// and the two are asserted equal when CHECK_DEF is on.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 10
static int n;
static uint32_t rows[MAXN];

static int perm[MAXN];
static long npm, pm_cap;
static int8_t (*pms)[MAXN];

static void dfs(int i, uint32_t used) {
    if (i == n) {
        if (npm >= pm_cap) { pm_cap *= 2; pms = realloc(pms, pm_cap * sizeof(*pms)); }
        for (int t = 0; t < n; t++) pms[npm][t] = (int8_t)perm[t];
        npm++;
        return;
    }
    uint32_t avail = rows[i] & ~used;
    while (avail) {
        int j = __builtin_ctz(avail); avail &= avail - 1;
        perm[i] = j; dfs(i + 1, used | (1u << j));
    }
}

static int acyclic(const uint32_t *adj, uint32_t V) {
    uint32_t rem = V;
    while (rem) {
        uint32_t hasin = 0, r = rem;
        while (r) { int i = __builtin_ctz(r); r &= r - 1; hasin |= adj[i] & rem; }
        uint32_t src = rem & ~hasin;
        if (!src) return 0;
        rem &= ~src;
    }
    return 1;
}

static uint32_t *subsets_by_pop; // subsets of [n] sorted by popcount
static int nsub;

static int forcing_fvs(const int8_t *p) {
    uint32_t adj[MAXN];
    for (int i = 0; i < n; i++) {
        adj[i] = 0;
        for (int j = 0; j < n; j++)
            if (i != j && ((rows[i] >> p[j]) & 1)) adj[i] |= 1u << j;
    }
    uint32_t full = (1u << n) - 1;
    for (int k = 0; k < nsub; k++) {
        uint32_t S = subsets_by_pop[k];
        if (acyclic(adj, full & ~S)) return __builtin_popcount(S);
    }
    return n;
}

// definition-based: S forcing iff every other pm q differs from p at some i in S
static int forcing_def(long idx) {
    const int8_t *p = pms[idx];
    // difference masks
    uint32_t *diff = malloc(sizeof(uint32_t) * (npm > 0 ? npm : 1));
    long nd = 0;
    for (long q = 0; q < npm; q++) {
        if (q == idx) continue;
        uint32_t d = 0;
        for (int i = 0; i < n; i++) if (pms[q][i] != p[i]) d |= 1u << i;
        diff[nd++] = d;
    }
    int ans = n;
    for (int k = 0; k < nsub; k++) {
        uint32_t S = subsets_by_pop[k];
        long t;
        for (t = 0; t < nd; t++) if (!(diff[t] & S)) break;
        if (t == nd) { ans = __builtin_popcount(S); break; }
    }
    free(diff);
    return ans;
}

static long count_graphs, count_tight, maxF[MAXN + 1], minF[MAXN + 1], pair_count[MAXN + 1][MAXN + 1];
static long min_defect = 1L << 40;
static int check_def = 0;

static void process_graph(void) {
    npm = 0; dfs(0, 0);
    if (npm == 0) return; // no perfect matching (cannot happen with diagonal present)
    int f = n + 1, F = -1;
    for (long q = 0; q < npm; q++) {
        int fv = forcing_fvs(pms[q]);
        if (check_def) {
            int fd = forcing_def(q);
            if (fd != fv) { fprintf(stderr, "MISMATCH fvs=%d def=%d\n", fv, fd); exit(2); }
        }
        if (fv < f) f = fv;
        if (fv > F) F = fv;
    }
    count_graphs++;
    long defect = (long)(f + 1) * (n - F) - n;
    if (defect < min_defect) min_defect = defect;
    if (defect < 0) {
        fprintf(stderr, "COUNTEREXAMPLE n=%d f=%d F=%d rows:", n, f, F);
        for (int i = 0; i < n; i++) fprintf(stderr, " %x", rows[i]);
        fprintf(stderr, "\n");
        exit(3);
    }
    if (defect == 0) count_tight++;
    if (F > maxF[f]) maxF[f] = F;
    if (F < minF[f]) minF[f] = F;
    pair_count[f][F]++;
}


static void compute_fF(int *fo, int *Fo) {
    npm = 0; dfs(0, 0);
    int f = n + 1, F = -1;
    for (long q = 0; q < npm; q++) { int fv = forcing_fvs(pms[q]); if (fv < f) f = fv; if (fv > F) F = fv; }
    *fo = f; *Fo = F;
}
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t xrand(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }
static double urand(void) { return (xrand() >> 11) * (1.0 / 9007199254740992.0); }

static void report(const char *mode) {
    printf("n=%d mode=%s graphs=%ld tight(equality)=%ld min_defect=%ld\n", n, mode, count_graphs, count_tight, min_defect);
    for (int f = 0; f <= n; f++) {
        if (maxF[f] < 0) continue;
        int bound = n - (n + f) / (f + 1); // n - ceil(n/(f+1))
        printf("  f=%d: observed F in [%ld,%ld], bound F<=%d %s\n", f, minF[f], maxF[f], bound,
               maxF[f] == bound ? "(attained)" : "");
    }
    printf("  (f,F) pairs:");
    for (int f = 0; f <= n; f++) for (int F = 0; F <= n; F++) if (pair_count[f][F]) printf(" (%d,%d):%ld", f, F, pair_count[f][F]);
    printf("\n");
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s n exhaustive|random [samples] [seed] [checkdef]\n", argv[0]); return 1; }
    n = atoi(argv[1]);
    const char *mode = argv[2];
    long samples = argc > 3 ? atol(argv[3]) : 1000;
    if (argc > 4) rng_state ^= (uint64_t)atol(argv[4]) * 0x9E3779B97F4A7C15ULL;
    check_def = argc > 5 ? atoi(argv[5]) : 0;
    pm_cap = 1024; pms = malloc(pm_cap * sizeof(*pms));
    nsub = 1 << n; subsets_by_pop = malloc(sizeof(uint32_t) * nsub);
    int k = 0;
    for (int pc = 0; pc <= n; pc++) for (uint32_t S = 0; S < (1u << n); S++) if (__builtin_popcount(S) == pc) subsets_by_pop[k++] = S;
    for (int f = 0; f <= n; f++) { maxF[f] = -1; minF[f] = n + 1; }


    if (!strcmp(mode, "input")) { // rows as hex: argv[3..3+n-1]
        for (int i = 0; i < n; i++) rows[i] = (uint32_t)strtoul(argv[3 + i], NULL, 16);
        int f, F; compute_fF(&f, &F);
        printf("n=%d f=%d F=%d pms=%ld defect=%ld bound_F=%d\n", n, f, F, npm, (long)(f + 1) * (n - F) - n, n - (n + f) / (f + 1));
        return 0;
    }
    if (!strcmp(mode, "climb")) { // argv[3]=target f, argv[4]=seed, argv[5]=iters
        int ft = atoi(argv[3]); long iters = atol(argv[5]);
        int best = -1; uint32_t bestrows[MAXN];
        for (int restart = 0; restart < 20; restart++) {
            double d = urand();
            for (int i = 0; i < n; i++) { rows[i] = 1u << i; for (int j = 0; j < n; j++) if (i != j && urand() < d) rows[i] |= 1u << j; }
            int f, F; compute_fF(&f, &F);
            long score = F - 3L * abs(f - ft);
            for (long it = 0; it < iters; it++) {
                int i = (int)(xrand() % n), j = (int)(xrand() % n); if (i == j) continue;
                uint32_t old = rows[i]; rows[i] ^= 1u << j;
                int f2, F2; compute_fF(&f2, &F2);
                long s2 = F2 - 3L * abs(f2 - ft);
                if (s2 >= score || urand() < 0.02) { score = s2; f = f2; F = F2; if (f == ft && F > best) { best = F; memcpy(bestrows, rows, sizeof(rows)); } }
                else rows[i] = old;
            }
        }
        printf("n=%d target f=%d: best F=%d (bound %d) rows:", n, ft, best, n - (n + ft) / (ft + 1));
        for (int i = 0; i < n; i++) printf(" %x", bestrows[i]);
        printf("\n");
        return 0;
    }
    if (!strcmp(mode, "exhaustive")) {
        int noff = n * (n - 1);
        for (uint64_t mask = 0; mask < (1ULL << noff); mask++) {
            for (int i = 0; i < n; i++) rows[i] = 1u << i;
            int bit = 0;
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) { if ((mask >> bit) & 1) rows[i] |= 1u << j; bit++; }
            process_graph();
        }
    } else {
        for (long s = 0; s < samples; s++) {
            int family = (int)(xrand() % 4);
            if (family == 0 || family == 1) { // random density
                double d = urand();
                for (int i = 0; i < n; i++) { rows[i] = 1u << i; for (int j = 0; j < n; j++) if (i != j && urand() < d) rows[i] |= 1u << j; }
            } else if (family == 2) { // K_{n,n} minus a few random edges (large F region)
                int r = (int)(xrand() % (2 * n + 1));
                for (int i = 0; i < n; i++) rows[i] = (1u << n) - 1;
                for (int t = 0; t < r; t++) { int i = (int)(xrand() % n), j = (int)(xrand() % n); if (i != j) rows[i] &= ~(1u << j); }
            } else { // upper-triangular (unique pm) plus a few random extra edges (small f region)
                double d = urand();
                int r = (int)(xrand() % (n + 1));
                for (int i = 0; i < n; i++) { rows[i] = 1u << i; for (int j = i + 1; j < n; j++) if (urand() < d) rows[i] |= 1u << j; }
                for (int t = 0; t < r; t++) { int i = (int)(xrand() % n), j = (int)(xrand() % n); rows[i] |= 1u << j; }
            }
            process_graph();
        }
    }
    report(mode);
    return 0;
}
