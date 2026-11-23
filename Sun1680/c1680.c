// Sun's 1680-conjecture (OEIS A280831): every 8m+7 is x^2+y^2+z^2+w^2 with x,y,z,w >= 1 and x^4 + 1680 y^3 z a square.
// Phase 1 lists every (x, y, z) with x^4 + 1680 y^3 z = t^2 and x^2 + y^2 + z^2 < N, without searching over x:
//   put u = t - x^2, v = t + x^2, M = 1680 y^3. Then u v = M z. With M1 = gcd(u, M), M2 = M / M1 we get
//   u = M1 u', v = M2 v', u' v' = z, gcd(u', M2) = 1, and M2 v' - M1 u' = 2 x^2.
//   So for each y, each pair (u', v') with u' v' <= sqrt(N), we look for the divisors M1 of M for which
//   M2 v' - M1 u' lies in [2, 2N] and is twice a square. Every solution arises exactly once.
// Phase 2 adds w^2 and counts, for each m with 8m+7 < N, the number of representations (saturating at 255).
// Usage: c1680 N threads [triples.bin]            all in one go (triples.bin: every triple, for checking)
//        c1680 N threads tri YLO YHI PREFIX      phase 1 for YLO <= y <= YHI only; writes PREFIX_A.bin, PREFIX_B.bin
//        c1680 N threads count PREFIX...         phase 2 from the files written by "tri" runs
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef unsigned __int128 u128; typedef __int128 i128; typedef uint64_t u64;
static u64 isqrt64(u64 x) { u64 r = (u64)sqrtl((long double)x); while (r * r > x) r--; while ((r + 1) * (r + 1) <= x) r++; return r; }
static u64 gcd128(u64 a, u128 b) { u64 r = (u64)(b % a); while (r) { u64 t = a % r; a = r; r = t; } return a; }
static int cmp128(const void *a, const void *b) { u128 x = *(const u128 *)a, y = *(const u128 *)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
    u64 N = strtoull(argv[1], 0, 10); int threads = atoi(argv[2]);
    u64 Y = isqrt64(N), Z = Y;
    uint32_t *spf = calloc(Y + 2, 4);
    for (u64 i = 2; i <= Y; i++) if (!spf[i]) for (u64 j = i; j <= Y; j += i) if (!spf[j]) spf[j] = (uint32_t)i;
    // output buffers per thread: s = x^2+y^2+z^2 for the triples usable for 8m+7, by type
    u64 **bufA = calloc(threads, sizeof(u64 *)), **bufB = calloc(threads, sizeof(u64 *)), *nA = calloc(threads, 8), *nB = calloc(threads, 8), *capA = calloc(threads, 8), *capB = calloc(threads, 8);
    u64 **all = calloc(threads, sizeof(u64 *)), *nall = calloc(threads, 8), *capall = calloc(threads, 8);
    int mode_tri = argc > 3 && !strcmp(argv[3], "tri"), mode_count = argc > 3 && !strcmp(argv[3], "count");
    int keep = argc > 3 && !mode_tri && !mode_count;
    u64 YLO = mode_tri ? strtoull(argv[4], 0, 10) : 1, YHI = mode_tri ? strtoull(argv[5], 0, 10) : Y; if (YHI > Y) YHI = Y;
    if (mode_count) YHI = 0;
    u64 total = 0;
    double t0 = omp_get_wtime();
    #pragma omp parallel num_threads(threads) reduction(+:total)
    {
        int tid = omp_get_thread_num();
        u128 *D = malloc(sizeof(u128) * 400000); long double *Dl = malloc(sizeof(long double) * 400000);
        #pragma omp for schedule(dynamic, 16)
        for (u64 y = YLO; y <= YHI; y++) {
            u64 yy = y * y; if (yy + 2 >= N) continue;
            // factor M = 1680 y^3 = 2^4 * 3 * 5 * 7 * y^3
            u64 pr[24]; int ex[24]; int np = 0; u64 r = y;
            while (r > 1) { u64 p = spf[r]; int e = 0; while (r % p == 0) { r /= p; e++; } pr[np] = p; ex[np++] = 3 * e; }
            static const u64 bp[4] = {2, 3, 5, 7}; static const int be[4] = {4, 1, 1, 1};
            for (int b = 0; b < 4; b++) { int f = 0; for (int i = 0; i < np; i++) if (pr[i] == bp[b]) { ex[i] += be[b]; f = 1; } if (!f) { pr[np] = bp[b]; ex[np++] = be[b]; } }
            u64 nd = 1; D[0] = 1;
            for (int i = 0; i < np; i++) { u64 cur = nd; u128 pw = 1; for (int e = 1; e <= ex[i]; e++) { pw *= pr[i]; for (u64 j = 0; j < cur; j++) D[nd++] = D[j] * pw; } }
            qsort(D, nd, sizeof(u128), cmp128);
            for (u64 i = 0; i < nd; i++) Dl[i] = (long double)D[i];
            u128 M = (u128)1680 * y * y * y; long double Ml = (long double)M;
            u64 xmax2 = N - 1 - yy;                               // x^2 + z^2 <= xmax2 - ... (z >= 1)
            long double Nl = (long double)xmax2;
            for (u64 up = 1; up <= Z; up++) {
                u64 vmax = Z / up;
                for (u64 vp = 1; vp <= vmax; vp++) {
                    u64 z = up * vp; if (z * z + 1 > xmax2) break;
                    // divisors M1 with 2 <= M*vp/M1 - M1*up <= 2*(xmax2 - z^2)
                    long double top = sqrtl(Ml * (long double)vp / (long double)up);         // f(M1) = 0
                    long double Wmax = 2.0L * (Nl - (long double)z * z);
                    long double lo = (-Wmax + sqrtl(Wmax * Wmax + 4.0L * Ml * (long double)z)) / (2.0L * (long double)up);  // f(M1) = Wmax
                    lo *= (1.0L - 1e-12L); long double hi = top * (1.0L + 1e-12L);
                    u64 a = 0, b = nd; while (a < b) { u64 m = (a + b) / 2; if (Dl[m] < lo) a = m + 1; else b = m; }
                    for (u64 i = a; i < nd && Dl[i] <= hi; i++) {
                        u128 M1 = D[i], M2 = M / M1;
                        u128 P = M2 * vp, Q = M1 * up; if (P <= Q) continue;
                        u128 Wv = P - Q; if (Wv & 1) continue;
                        u128 h = Wv >> 1; if (h > (u128)(xmax2 - z * z)) continue;
                        u64 x = isqrt64((u64)h); if ((u128)x * x != h || x == 0) continue;
                        if (gcd128(up, M2) != 1) continue;
                        u64 s = x * x + yy + z * z; if (s >= N) continue;
                        total++;
                        if (keep) { if (nall[tid] + 3 > capall[tid]) { capall[tid] = capall[tid] ? capall[tid] * 2 : 1 << 16; all[tid] = realloc(all[tid], capall[tid] * 8); } all[tid][nall[tid]++] = x; all[tid][nall[tid]++] = y; all[tid][nall[tid]++] = z; }
                        int odd = (int)(x & 1) + (int)(y & 1) + (int)(z & 1), two = ((x & 3) == 2) + ((y & 3) == 2) + ((z & 3) == 2);
                        if (odd == 3) { if (nA[tid] == capA[tid]) { capA[tid] = capA[tid] ? capA[tid] * 2 : 1 << 16; bufA[tid] = realloc(bufA[tid], capA[tid] * 8); } bufA[tid][nA[tid]++] = s; }
                        else if (odd == 2 && two == 1) { if (nB[tid] == capB[tid]) { capB[tid] = capB[tid] ? capB[tid] * 2 : 1 << 16; bufB[tid] = realloc(bufB[tid], capB[tid] * 8); } bufB[tid][nB[tid]++] = s; }
                    }
                }
            }
        }
    }
    u64 NA = 0, NB = 0; for (int t = 0; t < threads; t++) { NA += nA[t]; NB += nB[t]; }
    u64 *SA = malloc((NA + 1) * 8), *SB = malloc((NB + 1) * 8); u64 a = 0, b = 0;
    for (int t = 0; t < threads; t++) { memcpy(SA + a, bufA[t], nA[t] * 8); a += nA[t]; memcpy(SB + b, bufB[t], nB[t] * 8); b += nB[t]; }
    if (mode_count) {
        for (int i = 4; i < argc; i++) for (int type = 0; type < 2; type++) {
            char fn[1024]; snprintf(fn, sizeof fn, "%s_%c.bin", argv[i], type ? 'B' : 'A'); FILE *f = fopen(fn, "rb"); if (!f) { fprintf(stderr, "missing %s\n", fn); return 1; }
            fseek(f, 0, SEEK_END); u64 k = ftell(f) / 8; fseek(f, 0, SEEK_SET);
            if (type) { SB = realloc(SB, (NB + k + 1) * 8); if (fread(SB + NB, 8, k, f) != k) return 1; NB += k; } else { SA = realloc(SA, (NA + k + 1) * 8); if (fread(SA + NA, 8, k, f) != k) return 1; NA += k; }
            fclose(f); }
    }
    fprintf(stderr, "N = %llu: %llu triples (x,y,z) for y in [%llu,%llu]; usable for 8m+7: %llu all odd, %llu with one = 2 mod 4  [%.0fs]\n", (unsigned long long)N, (unsigned long long)total, (unsigned long long)YLO, (unsigned long long)YHI, (unsigned long long)NA, (unsigned long long)NB, omp_get_wtime() - t0);
    if (mode_tri) { char fn[1024];
        snprintf(fn, sizeof fn, "%s_A.bin", argv[6]); { FILE *f = fopen(fn, "wb"); fwrite(SA, 8, NA, f); fclose(f); }
        snprintf(fn, sizeof fn, "%s_B.bin", argv[6]); { FILE *f = fopen(fn, "wb"); fwrite(SB, 8, NB, f); fclose(f); }
        return 0; }
    if (keep) { FILE *f = fopen(argv[3], "wb"); for (int t = 0; t < threads; t++) fwrite(all[t], 8, nall[t], f); fclose(f); }
    // Phase 2: counts for m = (n - 7) / 8, n = s + w^2;  type A: w = 2 mod 4;  type B: w odd
    u64 Mn = (N - 7 + 7) / 8;                                    // m with 8m+7 < N  <=> m < (N - 7 + 7)/8 = N/8 (rounded up below)
    while (8 * Mn + 7 >= N) Mn--; Mn++;                           // number of m values: m = 0 .. Mn-1
    unsigned char *cnt = calloc(Mn + 1, 1);
    const u64 SEG = 1u << 20;                                     // m values per segment
    #pragma omp parallel for schedule(dynamic, 1) num_threads(threads)
    for (u64 seg = 0; seg < (Mn + SEG - 1) / SEG; seg++) {
        u64 m0 = seg * SEG, m1 = m0 + SEG < Mn ? m0 + SEG : Mn, A0 = 8 * m0 + 7, B0 = 8 * (m1 - 1) + 7;   // n in [A0, B0]
        for (int type = 0; type < 2; type++) {
            u64 *S = type ? SB : SA, ns = type ? NB : NA;
            for (u64 i = 0; i < ns; i++) {
                u64 s = S[i]; if (s + 1 > B0) continue;
                u64 wlo = s + 1 >= A0 ? 1 : isqrt64(A0 - s - 1) + 1, whi = isqrt64(B0 - s);
                if (type == 0) { while ((wlo & 3) != 2) wlo++; for (u64 w = wlo; w <= whi; w += 4) { u64 m = (s + w * w - 7) >> 3; if (cnt[m] != 255) cnt[m]++; } }
                else { wlo |= 1; for (u64 w = wlo; w <= whi; w += 2) { u64 m = (s + w * w - 7) >> 3; if (cnt[m] != 255) cnt[m]++; } }
            }
        }
    }
    fprintf(stderr, "counts done [%.0fs]\n", omp_get_wtime() - t0);
    printf("N = %llu: m = 0 .. %llu\n", (unsigned long long)N, (unsigned long long)(Mn - 1));
    printf("first terms a(0..19):"); for (u64 m = 0; m < 20 && m < Mn; m++) printf(" %d", cnt[m]); printf("\n");
    u64 nz = 0; for (u64 m = 0; m < Mn; m++) if (cnt[m] == 0) { nz++; if (nz <= 40) printf("ZERO: a(%llu) = 0, i.e. n = %llu\n", (unsigned long long)m, (unsigned long long)(8 * m + 7)); }
    printf("zeros: %llu\n", (unsigned long long)nz);
    for (u64 lo = 1000; lo < Mn; lo *= 10) { u64 hi = lo * 10 < Mn ? lo * 10 : Mn; u64 c[6] = {0}, last1 = 0; double sum = 0;
        for (u64 m = lo; m < hi; m++) { if (cnt[m] < 6) c[cnt[m]]++; if (cnt[m] == 1) last1 = m; sum += cnt[m]; }
        printf("  m in [%llu,%llu): mean %.1f (255 = saturated), #a=0: %llu, #a=1: %llu, #a=2: %llu, #a=3: %llu, last m with a=1: %llu\n", (unsigned long long)lo, (unsigned long long)hi, sum / (double)(hi - lo), (unsigned long long)c[0], (unsigned long long)c[1], (unsigned long long)c[2], (unsigned long long)c[3], (unsigned long long)last1); }
    { FILE *f = fopen("cnt1680.bin", "wb"); fwrite(cnt, 1, Mn, f); fclose(f); }
    return 0;
}
