# Sun's conjectures built from two exponentials (OEIS A234309, A234337, A234344, A234347, A234361):
#   a(n) = #{k : f(k, n-k) is prime} > 0 for all n > n0.
# For each n the candidates are grouped by their pair of exponents, sorted by size and tested until a prime is
# found.  "No prime" for an n means every candidate was tested and found composite (a small factor, or a failed
# strong-probable-prime test), which is a proof that a(n) = 0.
# Usage: e1scan.py FORM count N            full counts a(1..N), to compare with the OEIS table
#        e1scan.py FORM scan  N1 N2 [W]    report every n in [N1, N2] with a(n) = 0
#        e1scan.py FORM check n            test every candidate for one n and list the primes
import sys, time, math
import numpy as np
from gmpy2 import mpz, is_prime, gcd, primorial
from multiprocessing import Pool
PRIM = primorial(60000)
FORMS = {
 # name: (kmin(n), kmax(n), key(k, n, phi) -> (u, v) arrays + mask, value(u, v), bits(u, v), n0)
 'A234361': dict(k=lambda n: (1, n - 1), key=lambda k, n, phi: (phi[k] // 2, phi[n - k] // 4, (phi[k] % 2 == 0) & (phi[n - k] % 4 == 0)),
                 val=lambda u, v: (mpz(3) ** v << u) + 1, bits=lambda u, v: u + 1.585 * v, n0=7),
 'A234347': dict(k=lambda n: (1, n - 1), key=lambda k, n, phi: (k, phi[n - k] // 2, phi[n - k] % 2 == 0),
                 val=lambda u, v: mpz(3) ** u + mpz(3) ** v - 1, bits=lambda u, v: 1.585 * np.maximum(u, v), n0=3),
 'A234337': dict(k=lambda n: (1, n - 3), key=lambda k, n, phi: (2 * k, phi[n - k], phi[n - k] > 0),
                 val=lambda u, v: (mpz(1) << u) + (mpz(1) << v) - 1, bits=lambda u, v: np.maximum(u, v), n0=3),
 'A234344': dict(k=lambda n: (1, n - 1), key=lambda k, n, phi: (phi[k] // 2, phi[n - k] // 2, (phi[k] % 2 == 0) & (phi[n - k] % 2 == 0)),
                 val=lambda u, v: (mpz(1) << u) + mpz(3) ** v, bits=lambda u, v: np.maximum(u, 1.585 * v), n0=5),
 'A234309': dict(k=lambda n: (3, n // 2), key=lambda k, n, phi: (np.minimum(phi[k], phi[n - k]), np.maximum(phi[k], phi[n - k]), phi[k] > 0),
                 val=lambda u, v: (mpz(1) << u) + (mpz(1) << v) - 1, bits=lambda u, v: np.maximum(u, v), n0=5),
}
def totients(N):
    phi = np.arange(N + 1, dtype=np.int64)
    for i in range(2, N + 1):
        if phi[i] == i: phi[i::i] -= phi[i::i] // i
    return phi
cache = {}; PHI = None; F = None
def prime_pair(u, v):
    key = (u, v); r = cache.get(key)
    if r is None:
        x = F['val'](u, v)
        r = False if (x > 60000 and gcd(x, PRIM) != 1) else bool(is_prime(x, 2))
        cache[key] = r
    return r
def pairs(n):
    lo, hi = F['k'](n)
    if hi < lo: return np.zeros(0, dtype=np.int64), np.zeros(0, dtype=np.int64), np.zeros(0, dtype=np.int64)
    k = np.arange(lo, hi + 1); u, v, ok = F['key'](k, n, PHI); u = u[ok]; v = v[ok]
    key = u * (1 << 32) + v; uq, c = np.unique(key, return_counts=True)
    u = uq >> 32; v = uq & ((1 << 32) - 1); o = np.argsort(F['bits'](u, v), kind='stable')
    return u[o], v[o], c[o]
def count(n):
    u, v, c = pairs(n); return int(sum(int(cc) for uu, vv, cc in zip(u.tolist(), v.tolist(), c.tolist()) if prime_pair(uu, vv)))
def haswit(n):
    u, v, c = pairs(n)
    for i, (uu, vv) in enumerate(zip(u.tolist(), v.tolist())):
        if prime_pair(uu, vv): return n, True, i + 1, len(u)
    return n, False, len(u), len(u)
def init(name, N):
    global PHI, F; F = FORMS[name]; PHI = totients(N)
if __name__ == '__main__':
    name, mode = sys.argv[1], sys.argv[2]; t0 = time.time()
    if mode == 'count':
        N = int(sys.argv[3]); init(name, N); a = [count(n) for n in range(1, N + 1)]
        print(name, 'a(1..%d):' % N, a[:40]); print('n with a(n) = 0:', [n for n in range(1, N + 1) if a[n - 1] == 0])
        import json; json.dump(a, open(f'count_{name}_{N}.json', 'w'))
    elif mode == 'check':
        n = int(sys.argv[3]); init(name, n); u, v, c = pairs(n)
        pr = [(int(uu), int(vv)) for uu, vv in zip(u.tolist(), v.tolist()) if prime_pair(uu, vv)]
        print(f'{name}, n = {n}: {int(c.sum())} values of k give integer exponents, {len(u)} distinct exponent pairs, primes: {pr} -> a(n) = {"0" if not pr else "> 0"} [{time.time()-t0:.0f}s]')
    else:
        N1, N2 = int(sys.argv[3]), int(sys.argv[4]); W = int(sys.argv[5]) if len(sys.argv) > 5 else 4
        zeros = []; worst = (0, 0)
        with Pool(W, initializer=init, initargs=(name, N2)) as pool:
            for i, (n, ok, tested, tot) in enumerate(pool.imap(haswit, range(N1, N2 + 1), chunksize=8)):
                if not ok:
                    zeros.append(n); print(f'  ZERO: a({n}) = 0  ({tot} exponent pairs, all composite) [{time.time()-t0:.0f}s]', flush=True)
                    if 'first' in sys.argv: pool.terminate(); break
                if (i + 1) % 1000 == 0: print(f'  up to n = {n} [{time.time()-t0:.0f}s]', flush=True)
        print(f'RESULT {name}: n in [{N1},{N2}] with a(n) = 0: {zeros} [{time.time()-t0:.0f}s]')
