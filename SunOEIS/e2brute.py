# Brute-force check of Sun's exponential conjectures in A234451 / A234504, independent of any tabulated list:
# every exponent that occurs is tested directly for primality with GMP.
import sys
from fractions import Fraction
from gmpy2 import mpz, is_prime
from sympy import totient
def reps(n, a, b, f, cache):
    """list of (k, e) with 0 < k < n, e = phi(k)/a + phi(n-k)/b an integer and f(e) prime"""
    out = []
    for k in range(1, n):
        e = Fraction(PH[k], a) + Fraction(PH[n - k], b)
        if e.denominator != 1: continue
        e = int(e)
        if e not in cache: cache[e] = bool(is_prime(f(e), 25))
        if cache[e]: out.append((k, e))
    return out
forms = {
 'A234451(i): 2^e+3, /2,/6':      (2, 6, lambda e: (mpz(1) << e) + 3),
 'A234451(i\'): 2^e-3, /2,/6':    (2, 6, lambda e: (mpz(1) << e) - 3),
 'A234451(ii): 3*2^e+1, /2,/8':   (2, 8, lambda e: 3 * (mpz(1) << e) + 1),
 'A234451(ii): 3*2^e+1, /2,/12':  (2, 12, lambda e: 3 * (mpz(1) << e) + 1),
 'A234451(ii): 3*2^e-1, /2,/12':  (2, 12, lambda e: 3 * (mpz(1) << e) - 1),
 'A234504: 2^e-5, /1,/4':         (1, 4, lambda e: (mpz(1) << e) - 5),
}
mode = sys.argv[1]
if mode == 'small':
    N = int(sys.argv[2]); PH = [0] + [int(totient(i)) for i in range(1, N + 1)]
    for name, (a, b, f) in forms.items():
        cache = {}; cnt = [len(reps(n, a, b, f, cache)) for n in range(1, N + 1)]
        print(name, '| first 30 terms:', cnt[:30], '| n <=', N, 'with none:', [n for n in range(1, N + 1) if cnt[n - 1] == 0])
else:
    name = sys.argv[2]; n = int(sys.argv[3]); a, b, f = forms[name]
    PH = [0] + [int(totient(i)) for i in range(1, n + 1)]
    cache = {}; r = reps(n, a, b, f, cache)
    print(f'{name}, n = {n}: representations: {len(r)} {r[:5]} | distinct integer exponents tested: {len(cache)}, largest {max(cache)}, primes among them: {sorted(e for e in cache if cache[e])}')
