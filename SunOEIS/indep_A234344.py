# Independent check of a(n) = 0 for OEIS A234344:
#   a(n) = #{0 < k < n : 2^(phi(k)/2) + 3^(phi(n-k)/2) is prime}.
# Totients from sympy, primality from PARI (cypari, ispseudoprime = Baillie-PSW). No code shared with e1scan.py.
# Usage: indep_A234344.py n workers
import sys, time
from fractions import Fraction
from multiprocessing import Pool
from sympy import totient
n = int(sys.argv[1]); W = int(sys.argv[2])
def test(uv):
    import cypari
    u, v = uv
    return uv, bool(cypari.pari(f'ispseudoprime(2^{u}+3^{v})'))
if __name__ == '__main__':
    t0 = time.time(); ph = [0] + [int(totient(i)) for i in range(1, n)]
    pairs = {}; nk = 0
    for k in range(1, n):
        a = Fraction(ph[k], 2); b = Fraction(ph[n - k], 2)
        if a.denominator == 1 and b.denominator == 1:
            pairs[(int(a), int(b))] = pairs.get((int(a), int(b)), 0) + 1; nk += 1
    print(f'n = {n}: {nk} values of k have both exponents integral; {len(pairs)} distinct exponent pairs; largest number has about {max(max(u, 1.585 * v) for u, v in pairs):.0f} bits', flush=True)
    primes = []
    with Pool(W) as pool:
        for i, (uv, ok) in enumerate(pool.imap_unordered(test, sorted(pairs), chunksize=16)):
            if ok: primes.append(uv); print('  PRIME:', uv, flush=True)
            if (i + 1) % 4000 == 0: print(f'  {i + 1} tested [{time.time()-t0:.0f}s]', flush=True)
    print(f'RESULT n = {n}: exponent pairs giving a prime: {primes} -> a(n) = {sum(pairs[p] for p in primes)} [{time.time()-t0:.0f}s]')
