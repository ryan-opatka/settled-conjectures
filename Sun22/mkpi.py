# pi at the chunk boundaries used by fast22.c, computed with primecount.
import sys, math, primecountpy as pc
N = int(sys.argv[1]); TC = (1 << 22) * 2730
# p_N by primecount
pN = pc.nth_prime(N); need = N * (pN - 1) + 2000
nch = need // (6 * TC) + 1
with open(sys.argv[2], 'w') as f:
    for c in range(nch + 1): f.write(f'{6 * TC * c} {pc.prime_pi(6 * TC * c)}\n')
print('chunks', nch, 'X', 6 * TC * nch)
