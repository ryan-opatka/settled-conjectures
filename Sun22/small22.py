# Sun, Conjecture 2.2 of arXiv:1402.6641, brute force for n <= N.
#  (i)  some 0 < k < p_n has n | pi(k n)
#  (ii) { pi(k n) : k = 1..2 p_n } covers all residues mod n
import sys, numpy as np, math
N = int(sys.argv[1])
def primes_upto(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return s
# p_N upper bound
pb = int(N * (math.log(N) + math.log(math.log(N)) + 2)) + 50
s0 = primes_upto(pb); pl = np.nonzero(s0)[0]; assert len(pl) > N
pN = int(pl[N - 1]); X = 2 * N * pN
s = primes_upto(X); pi = np.cumsum(s, dtype=np.int32); del s
fail1 = []; fail2 = []; a = np.zeros(N + 1, dtype=np.int64); m2 = np.zeros(N + 1, dtype=np.int64)
for n in range(1, N + 1):
    p = int(pl[n - 1])
    v = pi[n * np.arange(1, 2 * p + 1)].astype(np.int64) % n
    a[n] = int((v[:p - 1] == 0).sum())
    if a[n] == 0: fail1.append(n)
    # least m with complete residue system
    first = np.full(n, -1, dtype=np.int64)
    idx = np.arange(len(v) - 1, -1, -1); first[v[::-1]] = idx   # earliest index for each residue
    if (first < 0).any(): fail2.append(n); m2[n] = 0
    else: m2[n] = int(first.max()) + 1
print('first terms of A237597:', a[1:21].tolist())
print('first terms of A237643:', m2[1:21].tolist())
print('(i) failures n <=', N, ':', fail1)
print('(ii) failures n <=', N, ':', fail2)
lam = np.array([pl[n-1] / n for n in range(1, N + 1)])
for lo, hi in ((10,100),(100,1000),(1000,N)):
    if hi <= N:
        seg = a[lo:hi+1]
        print(f'n in [{lo},{hi}]: mean count {seg.mean():.2f}, mean (p_n-1)/n {lam[lo-1:hi].mean():.2f}, #count=1: {(seg==1).sum()}, #count=0: {(seg==0).sum()}, expected zeros if Poisson: {np.exp(-lam[lo-1:hi]).sum():.2f}')
        r = m2[lo:hi+1] / (2 * pl[lo-1:hi]); print(f'    (ii): max of m/(2 p_n) = {r.max():.3f} at n = {lo + int(r.argmax())}')
np.save(f'a22_{N}.npy', a); np.save(f'm22_{N}.npy', m2)
