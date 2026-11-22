# Sun, Conjecture 2.4(i) (A237598): some 0 < k < p_n has pi(kn) a square; and the remark's variant:
# for n > 9 some 0 < k < p_n/2 has pi(kn) triangular.  Uses the tables written by fast22.
import sys, numpy as np, math
pre = sys.argv[1]; N = int(sys.argv[2])
q = np.fromfile(pre + '_psq.bin', dtype=np.uint64).astype(np.int64); S = len(q) // 2; A = q[:S].copy(); B = q[S:].copy()
t = np.fromfile(pre + '_ptr.bin', dtype=np.uint64).astype(np.int64); T = len(t) // 2; TA = t[:T].copy(); TB = t[T:].copy()
A[0] = 0; B[0] = 2; TA[0] = 0; TB[0] = 2                       # pi(x) = 0 for x < 2
m = int(N * (math.log(N) + math.log(math.log(N)) + 3)) + 100; s = np.ones(m + 1, dtype=bool); s[:2] = False
for i in range(2, int(m**0.5) + 1):
    if s[i]: s[i*i::i] = False
pl = np.nonzero(s)[0][:N]
def count(lo, hi, n, lim):
    # multiples of n in [lo_i, hi_i) and in [n, lim]
    f = np.maximum(-(-lo // n) * n, n); h = np.minimum(hi - 1, lim)
    return int(np.where(f <= h, (h - f) // n + 1, 0).sum())
sq = np.zeros(N + 1, dtype=np.int64); tr = np.zeros(N + 1, dtype=np.int64)
Sv = int(np.searchsorted(A[1:], 0, side='right'))                # entries that were filled
nS = int((A[1:] > 0).sum()) + 1; nT = int((TA[1:] > 0).sum()) + 1
for n in range(1, N + 1):
    p = int(pl[n - 1]); lim = n * (p - 1)
    j = int(np.searchsorted(A[:nS], lim, side='right'))
    assert j < nS - 1, 'table too short'
    sq[n] = count(A[:j], B[:j], n, lim)
    lim2 = n * ((p - 1) // 2)
    j = int(np.searchsorted(TA[:nT], lim2, side='right'))
    tr[n] = count(TA[:j], TB[:j], n, lim2)
print('first terms (A237598):', sq[1:21].tolist())
print('2.4(i) failures (no square):', (np.nonzero(sq[1:] == 0)[0] + 1).tolist()[:20])
z = np.nonzero(tr[1:] == 0)[0] + 1; print('triangular variant, failures with n > 9:', z[z > 9].tolist()[:20], '| n <= 9 without:', z[z <= 9].tolist())
for lo, hi in ((100, 1000), (1000, 10000), (10000, 100000), (100000, 1000000)):
    if hi <= N: print(f'  n in [{lo},{hi}]: squares: min {sq[lo:hi+1].min()}, #count=1: {(sq[lo:hi+1]==1).sum()}, mean {sq[lo:hi+1].mean():.1f} | triangular: min {tr[lo:hi+1].min()}, #count=1: {(tr[lo:hi+1]==1).sum()}, mean {tr[lo:hi+1].mean():.1f}')
np.save(pre + '_sq24.npy', sq); np.save(pre + '_tr24.npy', tr)
