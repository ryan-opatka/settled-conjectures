# Sun, Conjecture 4.5: every n > 7 is k + m (k, m >= 1) with p = p_k + phi(m) prime and q(p) - 1 prime;
# every n > 7, n != 15, likewise with q(p) + 1 prime.  (OEIS A234615, A234644.)
# Usage: python3 c45.py M     (uses q(r) for primes r <= M; checks every n with p_{n-1} + n <= M)
import sys, numpy as np, time
from gmpy2 import mpz, is_prime
from flint import fmpz
M = int(sys.argv[1]); t0 = time.time()
P = [int(fmpz(i).partitions_p()) for i in range(M // 2 + 1)]
def qval(m):                                   # Gauss: q(m) = sum of p((m - t)/2) over triangular t <= m, t = m (mod 2)
    s = 0; j = 0; t = 0
    while t <= m:
        if (m - t) % 2 == 0: s += P[(m - t) // 2]
        j += 1; t = j * (j + 1) // 2
    return s
class Q:                                       # q on demand, only primes are asked for
    def __getitem__(self, m): return qval(m)
q = Q()
isp = np.ones(M + 1, dtype=bool); isp[:2] = False
for i in range(2, int(M**0.5) + 1):
    if isp[i]: isp[i*i::i] = False
primes = np.nonzero(isp)[0]
phi = np.arange(M + 1, dtype=np.int64)
for i in primes: phi[i::i] -= phi[i::i] // i
Sm = np.zeros(M + 1, dtype=bool); Sp = np.zeros(M + 1, dtype=bool)
for r in primes:
    r = int(r)
    if is_prime(mpz(q[r]) - 1, 10): Sm[r] = True
    if is_prime(mpz(q[r]) + 1, 10): Sp[r] = True
print('primes r <= %d with q(r)-1 prime: %d ; with q(r)+1 prime: %d' % (M, Sm.sum(), Sp.sum()), f'[{time.time()-t0:.0f}s]', flush=True)
print(' first (q-1):', np.nonzero(Sm)[0][:15].tolist(), ' first (q+1):', np.nonzero(Sp)[0][:15].tolist())
# largest n with p_k + phi(m) <= M for all k + m = n:  p_{n-1} + n <= M
N = 1
while N + 1 < len(primes) and int(primes[N - 1]) + N + 1 <= M: N += 1
N -= 1
cm = np.zeros(N + 1, dtype=np.int64); cp = np.zeros(N + 1, dtype=np.int64)
for n in range(2, N + 1):
    k = np.arange(1, n); v = primes[k - 1] + phi[n - k]
    cm[n] = int(Sm[v].sum()); cp[n] = int(Sp[v].sum())
zm = np.nonzero(cm[2:] == 0)[0] + 2; zp = np.nonzero(cp[2:] == 0)[0] + 2
print('checked n up to', N)
print('q(p)-1: n with no representation:', zm.tolist()[:40])
print('q(p)+1: n with no representation:', zp.tolist()[:40])
for lo, hi in ((100, 1000), (1000, 3000), (3000, N)):
    if hi <= N: print(f'  [{lo},{hi}]: (q-1) mean {cm[lo:hi+1].mean():.1f} min {cm[lo:hi+1].min()} #=1: {(cm[lo:hi+1]==1).sum()} | (q+1) mean {cp[lo:hi+1].mean():.1f} min {cp[lo:hi+1].min()} #=1: {(cp[lo:hi+1]==1).sum()}')
