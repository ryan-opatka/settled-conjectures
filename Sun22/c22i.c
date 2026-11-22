// Sun, Conjecture 2.2(i) of arXiv:1402.6641 (OEIS A237597):
//   a(n) = #{ 0 < k < p_n : n | pi(k n) }.   Conjecture: a(n) > 0 for all n.
// n | pi(kn) with pi(kn) = jn  <=>  p_{jn} <= kn < p_{jn+1}.  So we walk through the primes in
// order and, for every index i = jn, count the multiples of n in [p_i, p_{i+1}) below n*p_n.
// Usage: c22i N out.bin
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
static u64 N, *pn, *cnt, *limit;      // pn[n] = p_n ; limit[n] = n*(p_n-1) = largest allowed kn
#define B (1u<<22)
static u64 *P; static u64 nP = 0, i0 = 1; // P[t] = p_{i0+t}
static u64 nlo = 1;
static void process(u64 m) {           // P[0..m] valid, handle indices i0 .. i0+m-1 (needs P[t+1])
    while (nlo <= N && limit[nlo] < P[0]) nlo++;   // n too small: all its allowed multiples are below P[0]
    for (u64 n = nlo; n <= N; n++) {
        u64 i = ((i0 + n - 1) / n) * n;
        for (; i < i0 + m; i += n) {
            u64 p = P[i - i0], q = P[i - i0 + 1];
            if (p > limit[n]) break;
            u64 f = ((p + n - 1) / n) * n;          // first multiple of n that is >= p
            u64 hi = q - 1 < limit[n] ? q - 1 : limit[n];
            if (f <= hi) cnt[n] += (hi - f) / n + 1;
        }
    }
}
static void push(u64 p) {
    P[nP++] = p;
    if (nP == B + 1) { process(B); i0 += B; P[0] = P[B]; nP = 1; }
}
int main(int argc, char **argv) {
    N = strtoull(argv[1], 0, 10);
    // p_n for n <= N
    u64 pb = (u64)(N * (log((double)N + 2) + log(log((double)N + 3)) + 3)) + 100;
    char *s0 = calloc(pb + 1, 1); pn = malloc((N + 2) * 8); u64 c = 0;
    for (u64 i = 2; i <= pb && c < N; i++) if (!s0[i]) { pn[++c] = i; for (u64 j = i * i; j <= pb; j += i) s0[j] = 1; }
    if (c < N) { fprintf(stderr, "bound too small\n"); return 1; }
    free(s0);
    cnt = calloc(N + 2, 8); limit = malloc((N + 2) * 8);
    for (u64 n = 1; n <= N; n++) limit[n] = n * (pn[n] - 1);
    u64 X = limit[N] + 2000;            // sieve a little further so that p_{i+1} exists
    u64 r = (u64)sqrt((double)X) + 2;
    char *sb = calloc(r + 1, 1); u64 nb = 0, *bp = malloc((r / 2 + 10) * 8), *nx = malloc((r / 2 + 10) * 8);
    for (u64 i = 3; i <= r; i += 2) if (!sb[i]) { bp[nb++] = i; for (u64 j = i * i; j <= r; j += 2 * i) sb[j] = 1; }
    P = malloc((B + 2) * 8);
    push(2);
    const u64 S = 1u << 20;             // odd numbers per segment
    char *seg = malloc(S);
    for (u64 b = 0; b < nb; b++) nx[b] = (bp[b] * bp[b] - 3) / 2;   // index of p^2 among odds 3,5,7,...
    u64 total = (X - 1) / 2;            // odd numbers 3..X  -> indices 0..total-1 (value = 2*idx+3)
    for (u64 lo = 0; lo < total; lo += S) {
        u64 hi = lo + S < total ? lo + S : total;
        memset(seg, 0, hi - lo);
        for (u64 b = 0; b < nb; b++) {
            u64 p = bp[b], j = nx[b];
            if (j >= hi) { if (p * p > 2 * hi + 3) break; else continue; }
            for (; j < hi; j += p) seg[j - lo] = 1;
            nx[b] = j;
        }
        for (u64 j = lo; j < hi; j++) if (!seg[j - lo]) push(2 * j + 3);
    }
    if (nP > 1) process(nP - 1);
    cnt[1] += 1;                         // k = 1: pi(1) = 0 is divisible by 1
    FILE *f = fopen(argv[2], "wb"); fwrite(cnt, 8, N + 1, f); fclose(f);
    u64 zeros = 0;
    for (u64 n = 1; n <= N; n++) if (cnt[n] == 0) { printf("a(%llu) = 0\n", (unsigned long long)n); zeros++; }
    printf("N = %llu, primes generated up to about %llu, zeros: %llu\n", (unsigned long long)N, (unsigned long long)X, (unsigned long long)zeros);
    printf("first terms:"); for (u64 n = 1; n <= 20 && n <= N; n++) printf(" %llu", (unsigned long long)cnt[n]); printf("\n");
    return 0;
}
