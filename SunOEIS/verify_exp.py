# Verify a(n) = 0 for one of Sun's exponential conjectures (A234451 (ii), A234504): for the given n, every
# exponent e = phi(k)/a + phi(n-k)/b (0 < k < n) that is an integer is collected, and f(e) is tested with GMP.
# A "composite" verdict of the strong-probable-prime test is a proof of compositeness, so "no prime found"
# does not depend on any tabulated list.
# Usage: verify_exp.py FORM n workers
import sys, time
from multiprocessing import Pool
from gmpy2 import mpz, is_prime
FORMS = {
 '3*2^e+1,/2,/8':  (2, 8,  lambda e: 3 * (mpz(1) << e) + 1),
 '3*2^e+1,/2,/12': (2, 12, lambda e: 3 * (mpz(1) << e) + 1),
 '2^e-5,/1,/4':    (1, 4,  lambda e: (mpz(1) << e) - 5),
 '2^e+3,/2,/6':    (2, 6,  lambda e: (mpz(1) << e) + 3),
}
form = sys.argv[1]; n = int(sys.argv[2]); W = int(sys.argv[3]); a, b, f = FORMS[form]
def test(e): return e, bool(is_prime(f(e), 2))
if __name__ == '__main__':
    t0 = time.time()
    phi = list(range(n + 1))
    for i in range(2, n + 1):
        if phi[i] == i:
            for j in range(i, n + 1, i): phi[j] -= phi[j] // i
    es = set(); nk = 0
    for k in range(1, n):
        num = b * phi[k] + a * phi[n - k]                 # e = num / (a b)
        if num % (a * b) == 0: es.add(num // (a * b)); nk += 1
    es = sorted(es, reverse=True)
    print(f'{form}, n = {n}: {nk} values of k give an integer exponent; {len(es)} distinct exponents, from {es[-1]} to {es[0]}', flush=True)
    primes = []
    with Pool(W) as pool:
        for i, (e, ok) in enumerate(pool.imap_unordered(test, es, chunksize=4)):
            if ok: primes.append(e); print('  PRIME for e =', e, flush=True)
            if (i + 1) % 2000 == 0: print(f'  {i + 1} tested [{time.time() - t0:.0f}s]', flush=True)
    print(f'RESULT {form}, n = {n}: exponents with f(e) prime: {sorted(primes)}  ->  a(n) = {"0" if not primes else "> 0"}  [{time.time() - t0:.0f}s]')
