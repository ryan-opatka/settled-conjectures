// Sun, Conjecture 2.2(ii) of arXiv:1402.6641 (OEIS A237643):
//   for every n, { pi(k n) : k = 1 .. 2 p_n } contains a complete system of residues mod n.
// Generalised bound: k <= floor(NUM * p_n / DEN)  (NUM/DEN = 2 is the conjecture).
// For every n and every multiple kn in range, pi(kn) is read off the sieve (rank query inside the
// current segment) and the residue pi(kn) mod n is marked in a bit set for n.
// Usage: fast22ii N pifile out.txt [threads] [NUM DEN]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64;
#define ST   (1ull << 22)
#define SEGW (ST * 2 / 64)
#define TCSEG 2730ull
#define TC   (ST * TCSEG)
static u64 N, *pn, *limit, X, nb, *bp, PATPER, nchunks, *pi0, *off, *bits;
static unsigned char *PAT;
static u64 isqrt64(u64 x) { u64 r = (u64)sqrt((double)x); while (r * r > x) r--; while ((r + 1) * (r + 1) <= x) r++; return r; }
int main(int argc, char **argv) {
    N = strtoull(argv[1], 0, 10);
    int threads = argc > 4 ? atoi(argv[4]) : 4;
    u64 NUM = argc > 6 ? strtoull(argv[5], 0, 10) : 2, DEN = argc > 6 ? strtoull(argv[6], 0, 10) : 1;
    u64 pb = (u64)(N * (log((double)N + 2) + log(log((double)N + 3)) + 3)) + 100;
    char *s0 = calloc(pb + 1, 1); pn = malloc((N + 2) * 8); u64 c0 = 0;
    for (u64 i = 2; i <= pb && c0 < N; i++) if (!s0[i]) { pn[++c0] = i; for (u64 j = i * i; j <= pb; j += i) s0[j] = 1; }
    free(s0);
    limit = malloc((N + 2) * 8); u64 need = 0;
    for (u64 n = 1; n <= N; n++) { limit[n] = n * (NUM * pn[n] / DEN); if (limit[n] > need) need = limit[n]; }
    nchunks = need / (6 * TC) + 1; X = nchunks * 6 * TC;
    u64 r = isqrt64(X + 36 * ST) + 2;
    char *sb = calloc(r + 1, 1); bp = malloc((r / 2 + 10) * 8); nb = 0;
    for (u64 i = 3; i <= r; i += 2) if (!sb[i]) { if (i >= 23) bp[nb++] = i; for (u64 j = i * i; j <= r; j += 2 * i) sb[j] = 1; }
    free(sb);
    PATPER = 5ull * 7 * 11 * 13 * 17 * 19;
    u64 patlen = PATPER + SEGW * 8 + 64; PAT = calloc(patlen, 1);
    { static const int sp[6] = {5, 7, 11, 13, 17, 19};
      for (u64 t = 0; t < patlen * 4; t++) { u64 a = 6 * t + 1, b = 6 * t + 5; int ca = 0, cb = 0;
        for (int z = 0; z < 6; z++) { if (a % sp[z] == 0) ca = 1; if (b % sp[z] == 0) cb = 1; }
        if (ca) PAT[(2 * t) >> 3] |= 1 << ((2 * t) & 7);
        if (cb) PAT[(2 * t + 1) >> 3] |= 1 << ((2 * t + 1) & 7); } }
    pi0 = malloc((nchunks + 2) * 8);
    { FILE *f = fopen(argv[2], "r"); if (!f) { fprintf(stderr, "no pi file: need pi(6*TC*c) for c = 0..%llu, 6*TC = %llu\n", (unsigned long long)nchunks, (unsigned long long)(6 * TC)); return 2; }
      for (u64 c = 0; c <= nchunks; c++) { unsigned long long a, v; if (fscanf(f, "%llu %llu", &a, &v) != 2 || a != 6 * TC * c) { fprintf(stderr, "bad pi file\n"); return 2; } pi0[c] = v; }
      fclose(f); }
    off = malloc((N + 2) * 8); u64 tot = 0;
    for (u64 n = 1; n <= N; n++) { off[n] = tot; tot += (n + 63) / 64; }
    bits = calloc(tot + 1, 8);
    int bad = 0;
    fprintf(stderr, "N=%llu X=%llu chunks=%llu bitset words=%llu\n", (unsigned long long)N, (unsigned long long)X, (unsigned long long)nchunks, (unsigned long long)tot);
    #pragma omp parallel num_threads(threads)
    {
        u64 *seg = malloc(SEGW * 8 + 64); uint32_t *cum = malloc((SEGW + 1) * 4);
        u64 *nx1 = malloc(nb * 8), *nx5 = malloc(nb * 8);
        #pragma omp for schedule(dynamic, 1)
        for (u64 ch = 0; ch < nchunks; ch++) {
            u64 lo = 6 * TC * ch;
            for (u64 b = 0; b < nb; b++) {
                u64 p = bp[b], L = p * p > lo ? p * p : lo, m0 = (L + p - 1) / p;
                u64 m1 = m0 + ((1 + 6 - m0 % 6) % 6), m5 = m0 + ((5 + 6 - m0 % 6) % 6);
                u64 na = p * m1, nb5 = p * m5;
                nx1[b] = 2 * (na / 6) + (na % 6 == 5); nx5[b] = 2 * (nb5 / 6) + (nb5 % 6 == 5);
            }
            u64 nlo; { u64 a = 1, b = N + 1; while (a < b) { u64 m = (a + b) / 2; if (limit[m] < lo) a = m + 1; else b = m; } nlo = a; }
            u64 before = pi0[ch];                     // primes < current segment start
            for (u64 sgi = 0; sgi < TCSEG; sgi++) {
                u64 t0 = TC * ch + sgi * ST, g0 = 2 * t0, g1 = g0 + 2 * ST, a = 6 * t0, b = a + 6 * ST;
                memcpy(seg, PAT + ((t0 / 4) % PATPER), SEGW * 8);
                if (t0 == 0) { seg[0] |= 1; static const int sp[6] = {5, 7, 11, 13, 17, 19};
                    for (int z = 0; z < 6; z++) { u64 g = 2 * (sp[z] / 6) + (sp[z] % 6 == 5); seg[g >> 6] &= ~(1ull << (g & 63)); } }
                for (u64 q = 0; q < nb; q++) {
                    u64 p2 = 2 * bp[q];
                    u64 g = nx1[q]; for (; g < g1; g += p2) seg[(g - g0) >> 6] |= 1ull << ((g - g0) & 63); nx1[q] = g;
                    g = nx5[q];     for (; g < g1; g += p2) seg[(g - g0) >> 6] |= 1ull << ((g - g0) & 63); nx5[q] = g;
                }
                uint32_t c = 0; for (u64 w = 0; w < SEGW; w++) { cum[w] = c; c += (uint32_t)__builtin_popcountll(~seg[w]); } cum[SEGW] = c;
                u64 base = before + (a == 0 ? 0 : 0);  // pi(a - 1) counting 2 and 3 separately below
                while (nlo <= N && limit[nlo] < a) nlo++;
                for (u64 n = nlo; n <= N; n++) {
                    u64 x = ((a + n - 1) / n) * n; if (x == 0) x = n;
                    u64 lim = limit[n] < b - 1 ? limit[n] : b - 1;
                    u64 *bs = bits + off[n];
                    for (; x <= lim; x += n) {
                        u64 t = x / 6, s = x - 6 * t;
                        u64 B = 2 * (t - t0) + (s >= 1) + (s >= 5);            // bits below B are the numbers <= x
                        u64 w = B >> 6, k = B & 63;
                        u64 pi = base + cum[w] + (u64)__builtin_popcountll(~seg[w] & ((1ull << k) - 1));
                        if (a == 0) pi += (x >= 2) + (x >= 3);                // 2 and 3 are not in the table
                        u64 rr = pi % n;
                        if (!((bs[rr >> 6] >> (rr & 63)) & 1)) __atomic_fetch_or(&bs[rr >> 6], 1ull << (rr & 63), __ATOMIC_RELAXED);
                    }
                }
                before += c; if (a == 0) before += 2;
            }
            if (before != pi0[ch + 1]) {
                #pragma omp critical
                { fprintf(stderr, "COUNT MISMATCH chunk %llu: %llu vs %llu\n", (unsigned long long)ch, (unsigned long long)before, (unsigned long long)pi0[ch + 1]); bad = 1; }
            }
        }
    }
    if (bad) { fprintf(stderr, "FAILED\n"); return 3; }
    FILE *f = fopen(argv[3], "w"); u64 nf = 0;
    for (u64 n = 1; n <= N; n++) { u64 c = 0; for (u64 w = 0; w < (n + 63) / 64; w++) c += (u64)__builtin_popcountll(bits[off[n] + w]);
        if (c != n) { fprintf(f, "%llu %llu\n", (unsigned long long)n, (unsigned long long)(n - c)); nf++; if (nf <= 30) printf("n = %llu: %llu residues missed\n", (unsigned long long)n, (unsigned long long)(n - c)); } }
    fclose(f);
    printf("N = %llu, bound k <= %llu*p_n/%llu, all chunk counts agree with primecount, failing n: %llu\n", (unsigned long long)N, (unsigned long long)NUM, (unsigned long long)DEN, (unsigned long long)nf);
    return 0;
}
