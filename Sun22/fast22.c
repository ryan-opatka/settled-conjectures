// Sun, Conjecture 2.2(i) of arXiv:1402.6641 (OEIS A237597), fast multi-threaded version.
//   a(n) = #{ 0 < k < p_n : n | pi(k n) }.
// n | pi(kn), pi(kn) = jn  <=>  p_{jn} <= kn < p_{jn+1}: walk the primes in order and, for every
// index i = jn, count the multiples of n in [p_i, p_{i+1}) that are <= n (p_n - 1).
// Also records pi(k^2) for all k, and the primes with index s^2, s^2+1, t(t+1)/2, t(t+1)/2+1.
// The number line is cut into chunks of 6*TC numbers; chunk c needs pi(6*TC*c), read from a file
// (computed with primecount) and checked against the sieve's own count for every chunk.
// Usage: fast22 N pifile outprefix [threads]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64;
#define ST   (1ull << 22)            // t-values per segment (t = n div 6); 2 bits each -> 1 MB
#define SEGW (ST * 2 / 64)           // 64-bit words per segment
#define TCSEG 2730ull                // segments per chunk (multiple of 5*7*13*... not needed); chunk = 6*ST*TCSEG numbers
#define TC   (ST * TCSEG)
#define BLK  (1u << 22)
static u64 N, *pn, *limit, X;
static u64 nb, *bp;                   // base primes >= 23
static unsigned char *PAT; static u64 PATPER;   // presieve pattern for 5,7,11,13,17,19 (period in bytes)
static u64 nchunks, *pi0;             // pi0[c] = pi(6*TC*c)
static u64 *pisq, KSQ;                // pisq[k] = pi(k^2)
static u64 *psq, *psq1, SS;           // p_{s^2}, p_{s^2+1}
static u64 *ptr, *ptr1, TT;           // p_{t(t+1)/2}, p_{t(t+1)/2+1}
static u64 isqrt64(u64 x) { u64 r = (u64)sqrt((double)x); while (r * r > x) r--; while ((r + 1) * (r + 1) <= x) r++; return r; }

typedef struct {
    u64 *P; u64 nP, i0;               // P[t] = prime with index i0 + t
    u64 *cnt, *nexti; u64 nlo;
    u64 ksq, sqv;                     // next k whose square has not been passed
    u64 s, t;                         // next s with s^2 >= current index ; next t with t(t+1)/2 >= current index
} ctx;

static void process(ctx *c, u64 m) {  // indices i0 .. i0+m-1, P[0..m] valid
    u64 *P = c->P, i0 = c->i0, end = i0 + m;
    while (c->nlo <= N && limit[c->nlo] < P[0]) c->nlo++;
    for (u64 n = c->nlo; n <= N; n++) {
        u64 i = c->nexti[n];
        if (i >= end) continue;
        u64 lim = limit[n];
        for (; i < end; i += n) {
            u64 p = P[i - i0];
            if (p > lim) { i = ~0ull - 2 * n; break; }
            u64 q = P[i - i0 + 1];
            u64 f = ((p + n - 1) / n) * n;
            u64 hi = q - 1 < lim ? q - 1 : lim;
            if (f <= hi) c->cnt[n] += (hi - f) / n + 1;
        }
        c->nexti[n] = i;
    }
}
static inline void emit(ctx *c, u64 p) {   // p has index c->i0 + c->nP
    u64 idx = c->i0 + c->nP;
    while (c->sqv < p) { pisq[c->ksq] = idx - 1; c->ksq++; c->sqv = c->ksq * c->ksq; }
    while (c->s * c->s + 1 < idx) c->s++;
    if (c->s <= SS) { if (c->s * c->s == idx) psq[c->s] = p; if (c->s * c->s + 1 == idx) psq1[c->s] = p; }
    if (c->s > 0 && c->s - 1 <= SS && (c->s - 1) * (c->s - 1) + 1 == idx) psq1[c->s - 1] = p;
    while (c->t * (c->t + 1) / 2 + 1 < idx) c->t++;
    if (c->t <= TT) { if (c->t * (c->t + 1) / 2 == idx) ptr[c->t] = p; if (c->t * (c->t + 1) / 2 + 1 == idx) ptr1[c->t] = p; }
    if (c->t > 0 && c->t - 1 <= TT && (c->t - 1) * c->t / 2 + 1 == idx) ptr1[c->t - 1] = p;
    c->P[c->nP++] = p;
    if (c->nP == BLK + 1) { process(c, BLK); c->i0 += BLK; c->P[0] = c->P[BLK]; c->nP = 1; }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
    N = strtoull(argv[1], 0, 10);
    int threads = argc > 4 ? atoi(argv[4]) : 4;
    u64 pb = (u64)(N * (log((double)N + 2) + log(log((double)N + 3)) + 3)) + 100;
    char *s0 = calloc(pb + 1, 1); pn = malloc((N + 2) * 8); u64 c0 = 0;
    for (u64 i = 2; i <= pb && c0 < N; i++) if (!s0[i]) { pn[++c0] = i; for (u64 j = i * i; j <= pb; j += i) s0[j] = 1; }
    if (c0 < N) { fprintf(stderr, "bound too small\n"); return 1; }
    free(s0);
    limit = malloc((N + 2) * 8);
    for (u64 n = 1; n <= N; n++) limit[n] = n * (pn[n] - 1);
    u64 need = limit[N] + 2000;
    nchunks = need / (6 * TC) + 1; X = nchunks * 6 * TC;
    // base primes
    u64 r = isqrt64(X + 6 * 6 * ST) + 2;
    char *sb = calloc(r + 1, 1); bp = malloc((r / 2 + 10) * 8); nb = 0;
    for (u64 i = 3; i <= r; i += 2) if (!sb[i]) { if (i >= 23) bp[nb++] = i; for (u64 j = i * i; j <= r; j += 2 * i) sb[j] = 1; }
    free(sb);
    // presieve pattern: bit 2t <-> 6t+1, bit 2t+1 <-> 6t+5 ; set bit = composite
    PATPER = 5ull * 7 * 11 * 13 * 17 * 19;          // t-period; 2 bits per t -> period of 2*PATPER bits; in bytes: PATPER (4 periods)
    u64 patlen = PATPER + SEGW * 8 + 64;
    PAT = calloc(patlen, 1);
    { static const int sp[6] = {5, 7, 11, 13, 17, 19};
      for (u64 t = 0; t < patlen * 4; t++) { u64 a = 6 * t + 1, b = 6 * t + 5; int ca = 0, cb = 0;
        for (int z = 0; z < 6; z++) { if (a % sp[z] == 0) ca = 1; if (b % sp[z] == 0) cb = 1; }
        if (ca) PAT[(2 * t) >> 3] |= 1 << ((2 * t) & 7);
        if (cb) PAT[(2 * t + 1) >> 3] |= 1 << ((2 * t + 1) & 7); } }
    // pi at chunk starts
    pi0 = malloc((nchunks + 2) * 8);
    { FILE *f = fopen(argv[2], "r"); if (!f) { fprintf(stderr, "no pi file; chunk size %llu numbers, %llu chunks\n", (unsigned long long)(6 * TC), (unsigned long long)nchunks); return 2; }
      for (u64 c = 0; c <= nchunks; c++) { unsigned long long a, v; if (fscanf(f, "%llu %llu", &a, &v) != 2 || a != 6 * TC * c) { fprintf(stderr, "bad pi file at chunk %llu\n", (unsigned long long)c); return 2; } pi0[c] = v; }
      fclose(f); }
    KSQ = isqrt64(X) + 2; pisq = calloc(KSQ + 2, 8);
    SS = isqrt64(pi0[nchunks]) + 2; psq = calloc(SS + 2, 8); psq1 = calloc(SS + 2, 8);
    TT = isqrt64(2 * pi0[nchunks]) + 2; ptr = calloc(TT + 2, 8); ptr1 = calloc(TT + 2, 8);
    u64 *cntall = calloc((N + 2) * (u64)threads, 8);
    int bad = 0;
    fprintf(stderr, "N=%llu X=%llu chunks=%llu base primes=%llu threads=%d\n", (unsigned long long)N, (unsigned long long)X, (unsigned long long)nchunks, (unsigned long long)nb, threads);
    #pragma omp parallel num_threads(threads)
    {
        int tid = omp_get_thread_num();
        ctx c; c.P = malloc((BLK + 2) * 8); c.cnt = cntall + (u64)tid * (N + 2); c.nexti = malloc((N + 2) * 8);
        u64 *seg = malloc(SEGW * 8 + 64);
        u64 *nx1 = malloc(nb * 8), *nx5 = malloc(nb * 8);
        #pragma omp for schedule(dynamic, 1)
        for (u64 ch = 0; ch < nchunks; ch++) {
            u64 lo = 6 * TC * ch, hi = lo + 6 * TC;
            c.nP = 0; c.i0 = pi0[ch] + 1; c.nlo = 1;
            { u64 a = 1, b = N + 1; while (a < b) { u64 m = (a + b) / 2; if (limit[m] < lo) a = m + 1; else b = m; } c.nlo = a; }
            for (u64 n = c.nlo; n <= N; n++) c.nexti[n] = ((c.i0 + n - 1) / n) * n;
            c.ksq = isqrt64(lo); if (c.ksq * c.ksq < lo) c.ksq++; if (c.ksq == 0) c.ksq = 1; c.sqv = c.ksq * c.ksq;
            c.s = isqrt64(c.i0); if (c.s * c.s < c.i0) { if (c.s * c.s + 1 < c.i0) c.s++; }
            c.t = 0; { u64 tt = isqrt64(2 * c.i0); if (tt > 2) tt -= 2; else tt = 0; while (tt * (tt + 1) / 2 + 1 < c.i0) tt++; c.t = tt; }
            // next positions (global bit index) for each base prime
            for (u64 b = 0; b < nb; b++) {
                u64 p = bp[b], L = p * p > lo ? p * p : lo, m0 = (L + p - 1) / p;
                u64 m1 = m0 + ((1 + 6 - m0 % 6) % 6), m5 = m0 + ((5 + 6 - m0 % 6) % 6);   // m = 1, 5 mod 6
                u64 na = p * m1, nb5 = p * m5;                                           // p*m1 = p mod 6 ; p*m5 = 5p mod 6
                u64 ga = 2 * (na / 6) + (na % 6 == 5), gb = 2 * (nb5 / 6) + (nb5 % 6 == 5);
                nx1[b] = ga; nx5[b] = gb;
            }
            if (ch == 0) { static const u64 sm[8] = {2, 3, 5, 7, 11, 13, 17, 19}; for (int z = 0; z < 8; z++) emit(&c, sm[z]); }
            u64 owned = 0; int done = 0;
            for (u64 sgi = 0; !done; sgi++) {             // one extra segment may be needed for the lookahead prime
                u64 t0 = TC * ch + sgi * ST, g0 = 2 * t0, g1 = g0 + 2 * ST;
                memcpy(seg, PAT + ((t0 / 4) % PATPER), SEGW * 8);
                if (t0 == 0) seg[0] |= 1;                 // the number 1
                for (u64 b = 0; b < nb; b++) {
                    u64 p2 = 2 * bp[b];
                    u64 g = nx1[b]; for (; g < g1; g += p2) seg[(g - g0) >> 6] |= 1ull << ((g - g0) & 63); nx1[b] = g;
                    g = nx5[b];     for (; g < g1; g += p2) seg[(g - g0) >> 6] |= 1ull << ((g - g0) & 63); nx5[b] = g;
                }
                for (u64 w = 0; w < SEGW && !done; w++) {
                    u64 v = ~seg[w];
                    while (v) {
                        u64 bit = (u64)__builtin_ctzll(v); v &= v - 1;
                        u64 g = g0 + w * 64 + bit, p = 6 * (g >> 1) + ((g & 1) ? 5 : 1);
                        if (p >= hi) {                    // lookahead prime: finish the chunk
                            while (c.sqv < hi) { pisq[c.ksq] = c.i0 + c.nP - 1; c.ksq++; c.sqv = c.ksq * c.ksq; }
                            c.P[c.nP] = p; if (c.nP > 0) process(&c, c.nP);
                            done = 1; break;
                        }
                        emit(&c, p); owned++;
                    }
                }
            }
            if (ch == 0) owned += 8;
            if (owned != pi0[ch + 1] - pi0[ch]) {
                #pragma omp critical
                { fprintf(stderr, "COUNT MISMATCH chunk %llu: sieve %llu, primecount %llu\n", (unsigned long long)ch, (unsigned long long)owned, (unsigned long long)(pi0[ch + 1] - pi0[ch])); bad = 1; }
            }
        }
    }
    if (bad) { fprintf(stderr, "FAILED\n"); return 3; }
    ptr[1] = 2;                           // index 1 = T(1) is also T(0)+1, which the bookkeeping above files under t = 0
    u64 *cnt = calloc(N + 2, 8);
    for (int t = 0; t < threads; t++) for (u64 n = 1; n <= N; n++) cnt[n] += cntall[(u64)t * (N + 2) + n];
    cnt[1] += 1;
    char fn[512];
    snprintf(fn, sizeof fn, "%s_a.bin", argv[3]);   { FILE *f = fopen(fn, "wb"); fwrite(cnt, 8, N + 1, f); fclose(f); }
    snprintf(fn, sizeof fn, "%s_pisq.bin", argv[3]); { FILE *f = fopen(fn, "wb"); fwrite(pisq, 8, isqrt64(X) + 1, f); fclose(f); }
    snprintf(fn, sizeof fn, "%s_psq.bin", argv[3]);  { FILE *f = fopen(fn, "wb"); fwrite(psq, 8, SS + 1, f); fwrite(psq1, 8, SS + 1, f); fclose(f); }
    snprintf(fn, sizeof fn, "%s_ptr.bin", argv[3]);  { FILE *f = fopen(fn, "wb"); fwrite(ptr, 8, TT + 1, f); fwrite(ptr1, 8, TT + 1, f); fclose(f); }
    u64 zeros = 0;
    for (u64 n = 1; n <= N; n++) if (cnt[n] == 0) { printf("a(%llu) = 0\n", (unsigned long long)n); zeros++; }
    printf("N = %llu, primes up to %llu, all %llu chunk counts agree with primecount, zeros: %llu\n", (unsigned long long)N, (unsigned long long)X, (unsigned long long)nchunks, (unsigned long long)zeros);
    printf("first terms:"); for (u64 n = 1; n <= 20 && n <= N; n++) printf(" %llu", (unsigned long long)cnt[n]); printf("\n");
    return 0;
}
