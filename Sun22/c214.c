// Sun, Conjecture 2.14(i) of arXiv:1402.6641: for every n the set { pi(k^2) : k = 1 .. 2 p_{n+1} - 3 }
// contains a complete system of residues modulo n.  Reads the table pi(k^2) written by fast22.
// Usage: c214 pisq.bin [threads]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
typedef uint64_t u64;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); fseek(f, 0, SEEK_END); u64 K = ftell(f) / 8 - 1; fseek(f, 0, SEEK_SET);
    u64 *ps = malloc((K + 1) * 8); if (fread(ps, 8, K + 1, f) != K + 1) return 1; fclose(f);
    int threads = argc > 2 ? atoi(argv[2]) : 4;
    u64 m = K / 2 + 100; char *s = calloc(m + 1, 1); u64 *pl = malloc((m / 2 + 10) * 8), np = 0;
    for (u64 i = 2; i <= m; i++) if (!s[i]) { pl[np++] = i; for (u64 j = i * i; j <= m; j += i) s[j] = 1; }
    u64 N = 0; while (N + 1 < np && 2 * pl[N + 1] - 3 <= K) N++;      // pl[n] = p_{n+1}; largest n with 2 p_{n+1} - 3 <= K
    double *ratio = calloc(N + 2, sizeof(double)); u64 *missed = calloc(N + 2, 8);
    #pragma omp parallel num_threads(threads)
    {
        u64 *first = malloc((N + 2) * 8);
        #pragma omp for schedule(dynamic, 64)
        for (u64 n = 1; n <= N; n++) {
            u64 kk = 2 * pl[n] - 3, seen = 0, last = 0;
            memset(first, 0, n * 8);
            for (u64 k = 1; k <= kk; k++) { u64 r = ps[k] % n; if (!first[r]) { first[r] = k; seen++; last = k; if (seen == n) break; } }
            missed[n] = n - seen; ratio[n] = (double)last / (double)kk;
        }
    }
    u64 nf = 0; printf("checked n = 1 .. %llu (table has pi(k^2) for k <= %llu)\n", (unsigned long long)N, (unsigned long long)K);
    for (u64 n = 1; n <= N; n++) if (missed[n]) { nf++; if (nf <= 30) printf("FAIL n = %llu: %llu residues missed (bound k <= %llu)\n", (unsigned long long)n, (unsigned long long)missed[n], (unsigned long long)(2 * pl[n] - 3)); }
    printf("failures: %llu\n", (unsigned long long)nf);
    for (int rep = 0; rep < 6; rep++) { u64 b = 0; for (u64 n = 1; n <= N; n++) if (!missed[n] && ratio[n] > ratio[b] ) b = n; if (!b) break;
        printf("  closest: n = %llu needs k up to %.4f of the bound\n", (unsigned long long)b, ratio[b]); ratio[b] = 0; }
    return 0;
}
