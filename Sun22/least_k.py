# Least k > 0 with n | pi(kn) (OEIS A237614), for one n, starting the search at a given j (pi(kn) = jn).
# Usage: least_k.py n [j_start]
import sys, primecountpy as pc
from gmpy2 import next_prime, mpz
n = int(sys.argv[1]); j = int(sys.argv[2]) if len(sys.argv) > 2 else 1
p = pc.nth_prime(n)
while True:
    lo = pc.nth_prime(j * n); hi = int(next_prime(mpz(lo))); f = -(-lo // n) * n
    if f < hi:
        k = f // n
        print(f'n = {n}: p_n = {p}; first hit at j = {j}: pi({k}*{n}) = pi({f}) = {j}*{n} = {j * n} (check: {pc.prime_pi(f)}); k = {k}, k/p_n = {k / p:.4f}')
        break
    j += 1
