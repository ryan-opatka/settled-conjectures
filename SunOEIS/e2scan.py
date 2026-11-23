# Sun's conjectures of the form: for every n > n0 some 0 < k < n has  e = phi(k)/a + phi(n-k)/b  an integer in S,
# where S is the set of exponents e for which some exponential expression is prime (taken from the OEIS).
# Needs a local copy of the OEIS data (https://github.com/oeis/oeisdata); set OEISDATA to its path.
import sys, re, os, numpy as np, time
N = int(sys.argv[1])
def terms(a):
    s = open(os.path.join(os.environ.get('OEISDATA', 'oeisdata'), 'seq', a[:4], a + '.seq')).read()
    return [int(x) for l in s.splitlines() if l[:2] in ('%S', '%T', '%U') for x in l[11:].split(',') if x.strip()]
phi = np.arange(N + 1, dtype=np.int64)
for i in range(2, N + 1):
    if phi[i] == i: phi[i::i] -= phi[i::i] // i
def div(c):
    r = np.where(phi % c == 0, phi // c, -1); r[0] = -1; return r
def count(S, A, B):
    """number of k in 1..n-1 with A[k] + B[n-k] in S (entries -1 excluded)"""
    cnt = np.zeros(N + 1, dtype=np.int64); S = [t for t in S if t >= 1]
    maxv = max(S); ks = np.arange(1, N + 1); v = A[1:]
    ok = (v >= 0) & (v <= maxv); ks = ks[ok]; v = v[ok]; o = np.argsort(v, kind='stable'); ks = ks[o]; v = v[o]
    start = np.searchsorted(v, np.arange(maxv + 2))
    js = np.arange(1, N + 1); Bj = B[1:]; ok = Bj >= 0; js = js[ok]; Bj = Bj[ok]
    for t in S:
        w = t - Bj; okw = (w >= 0) & (w <= maxv); j2 = js[okw]; w = w[okw]
        c = start[w + 1] - start[w]; nz = c > 0; j2 = j2[nz]; w = w[nz]; c = c[nz]
        if len(j2) == 0: continue
        jrep = np.repeat(j2, c); base = np.repeat(start[w], c); within = np.arange(len(jrep)) - np.repeat(np.cumsum(c) - c, c)
        n = ks[base + within] + jrep; cnt += np.bincount(n[n <= N], minlength=N + 1)
    return cnt
cases = [  # name, S sequence, a, b, n0, Sun verified to
 ('A234451 (i)  2^e+3,   e=phi(k)/2+phi(m)/6',  'A057732', 2, 6, 9, 50000),
 ('A234451 (i\') 2^e-3,   e=phi(k)/2+phi(m)/6',  'A050414', 2, 6, 13, 50000),
 ('A234451 (ii) 3*2^e+1, e=phi(k)/2+phi(m)/8',  'A002253', 2, 8, 25, 50000),
 ('A234451 (ii) 3*2^e+1, e=phi(k)/2+phi(m)/12', 'A002253', 2, 12, 38, 50000),
 ('A234451 (ii) 3*2^e-1, e=phi(k)/2+phi(m)/12', 'A002235', 2, 12, 14, 50000),
 ('A234504      2^e-5,   e=phi(k)+phi(m)/4',    'A059608', 1, 4, 10, 50000),
 ('A236358 (i)  2*3^e+1, e=phi(k)/2+phi(m)/12', 'A003306', 2, 12, 26, 50000),
 ('A236358 (ii) 2*3^e-1, e=phi(k)/2+phi(m)/12', 'A003307', 2, 12, 37, 50000),
]
for name, sq, a, b, n0, ver in cases:
    S = terms(sq); smax = max(S)
    lim = min(N, int(smax / (1.0 / a + 1.0 / b)))     # beyond this, exponents above the known list are attainable
    cnt = count(S, div(a), div(b))
    if a == 2:                                    # k = 1, 2: phi(k)/2 = 1/2, so e is an integer when phi(n-k) = b/2 (mod b)
        Sset = set(S)
        for k in (1, 2):
            f = phi[1:N + 1 - k]                   # phi(n-k) for n = k+1 .. N
            ok = f % b == b // 2
            e = (f + b // 2) // b
            hit = ok & np.isin(e, np.array(S))
            cnt[k + 1:N + 1] += hit.astype(np.int64)
    z = np.nonzero(cnt[n0 + 1:lim + 1] == 0)[0] + n0 + 1
    one = np.nonzero(cnt[n0 + 1:lim + 1] == 1)[0] + n0 + 1
    print(f'{name} [S={sq}, {len(S)} terms up to {smax}; scan valid to n={lim}]')
    print(f'   first terms {cnt[1:16].tolist()} | zeros beyond n0: {len(z)}, first {z[:8].tolist()} | a(n)=1: {len(one)}, last {one[-3:].tolist()} | mean near 5e4: {cnt[40000:50001].mean():.1f}', flush=True)
