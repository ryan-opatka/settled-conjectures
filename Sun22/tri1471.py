# A counterexample to a conjecture of Z.-W. Sun (remark after Conjecture 2.4 of arXiv:1402.6641,
# and Conjecture (ii) of OEIS A237598):
#   for every n > 9 there is a positive integer k < p_n / 2 such that pi(kn) is a triangular number.
# It fails at n = 1471: p_1471 = 12301, and the least k with pi(1471 k) triangular is 6321 > 12301 / 2.
# Two independent computations of pi: primecount, and a plain sieve written here.
# Usage: python3 tri1471.py [N]     checks every n <= N (default 3000)
import sys, math
import numpy as np
import primecountpy as pc

def tri(v):
    r = math.isqrt(8 * v + 1)
    return r * r == 8 * v + 1

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000

# 1. primecount
bad1 = []
for n in range(1, N + 1):
    p = pc.nth_prime(n)
    if not any(tri(pc.prime_pi(k * n)) for k in range(1, (p + 1) // 2) if 2 * k < p):
        bad1.append(n)

# 2. plain sieve
pb = int(N * (math.log(N + 2) + math.log(math.log(N + 3)) + 3)) + 100
s = np.ones(pb + 1, dtype=bool); s[:2] = False
for i in range(2, int(pb ** 0.5) + 1):
    if s[i]: s[i * i::i] = False
pl = np.nonzero(s)[0]
X = N * int(pl[N - 1]) // 2 + N
s = np.ones(X + 1, dtype=bool); s[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if s[i]: s[i * i::i] = False
pi = np.cumsum(s, dtype=np.int64)
bad2 = []
for n in range(1, N + 1):
    p = int(pl[n - 1])
    v = pi[n * np.arange(1, (p - 1) // 2 + 1)] if p > 2 else np.array([], dtype=np.int64)
    r = np.sqrt(8 * v + 1).astype(np.int64)
    r = np.where((r + 1) * (r + 1) <= 8 * v + 1, r + 1, r)
    if not (r * r == 8 * v + 1).any(): bad2.append(n)

print('n <= %d with no k < p_n/2 such that pi(kn) is triangular' % N)
print('  primecount:', bad1)
print('  own sieve :', bad2)
n = 1471; p = pc.nth_prime(n)
ks = [k for k in range(1, p) if tri(pc.prime_pi(k * n))]
print('n = 1471: p_n = %d, all k < p_n with pi(1471 k) triangular: %s' % (p, ks))
sys.exit(0 if bad1 == bad2 else 1)
