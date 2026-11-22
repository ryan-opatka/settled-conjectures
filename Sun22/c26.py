# Sun, Conjecture 2.6(ii) (A238902): for every n,
#   (a) pi(pi(kn)) is a square for some k = 1..n ;
#   (b) pi(pi(kn)) is a triangular number for some k <= (n+1)/2.
# pi(pi(x)) = v exactly for x in [P(v), P'(v)) with P(v) = p_{p_v}, P'(v) = p_{p_{v+1}}  (v >= 1);
# pi(pi(x)) = 0 for x < 3.  The interval ends come from primecount's nth_prime.
import sys, math, numpy as np, primecountpy as pc, time
N = int(sys.argv[1]); t0 = time.time()
def ends(v):
    if v == 0: return 0, 3
    a = pc.nth_prime(v); b = pc.nth_prime(v + 1)
    return pc.nth_prime(a), pc.nth_prime(b)
def table(vals, xmax):
    A = []; B = []
    for v in vals:
        a, b = ends(v)
        if a > xmax: break
        A.append(a); B.append(b)
    return np.array(A, dtype=np.int64), np.array(B, dtype=np.int64)
SA, SB = table((s * s for s in range(0, 10**9)), N * N)
TA, TB = table((t * (t + 1) // 2 for t in range(0, 10**9)), N * ((N + 1) // 2))
print('tables:', len(SA), 'squares,', len(TA), 'triangular', f'[{time.time()-t0:.0f}s]', flush=True)
np.save(f'c26_S_{N}.npy', np.stack([SA, SB])); np.save(f'c26_T_{N}.npy', np.stack([TA, TB]))
def count(A, B, n, lim):
    j = int(np.searchsorted(A, lim, side='right'))
    f = np.maximum(-(-A[:j] // n) * n, n); h = np.minimum(B[:j] - 1, lim)
    return int(np.where(f <= h, (h - f) // n + 1, 0).sum())
a = np.zeros(N + 1, dtype=np.int64); b = np.zeros(N + 1, dtype=np.int64)
for n in range(1, N + 1):
    a[n] = count(SA, SB, n, n * n); b[n] = count(TA, TB, n, n * ((n + 1) // 2))
print('first terms (A238902):', a[1:21].tolist())
print('(a) n with no square:', (np.nonzero(a[1:] == 0)[0] + 1).tolist()[:20])
print('(b) n with no triangular:', (np.nonzero(b[1:] == 0)[0] + 1).tolist()[:20])
for lo, hi in ((100, 1000), (1000, 10000), (10000, 100000), (100000, 200000), (200000, 1000000), (1000000, 3000000)):
    if hi <= N:
        x = a[lo:hi+1]; y = b[lo:hi+1]
        print(f'  [{lo},{hi}]: squares mean {x.mean():.2f} min {x.min()} #=1: {(x==1).sum()} #=2: {(x==2).sum()} | triangular mean {y.mean():.2f} min {y.min()} #=1: {(y==1).sum()} #=2: {(y==2).sum()}')
np.save(f'c26_a_{N}.npy', a); np.save(f'c26_b_{N}.npy', b)
print('done', f'[{time.time()-t0:.0f}s]')
