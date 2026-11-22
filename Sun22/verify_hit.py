# Independent check that a(n) = 0 for one n in Sun's Conjecture 2.2(i) (OEIS A237597):
#   there is no 0 < k < p_n with n | pi(kn).
# n | pi(kn) with pi(kn) = jn  <=>  p_{jn} <= kn < p_{jn+1}.  For every j with p_{jn} <= n (p_n - 1) we get
# p_{jn} from primecount's nth_prime and p_{jn+1} from GMP's next_prime, and look for a multiple of n between.
# Usage: verify_hit.py n workers      (writes verify_<n>_<r>.txt for each worker r)
import sys, os, time
from multiprocessing import Process
n = int(sys.argv[1]); W = int(sys.argv[2])
def work(r):
    os.environ['OMP_NUM_THREADS'] = '1'
    import primecountpy as pc
    from gmpy2 import next_prime, mpz, is_prime
    p = pc.nth_prime(n); lim = n * (p - 1)
    hits = []; best = None; cnt = 0; j = r if r > 0 else W; t0 = time.time()
    while True:
        lo = pc.nth_prime(j * n)
        if lo > lim: break
        hi = int(next_prime(mpz(lo)))
        f = -(-lo // n) * n                          # first multiple of n that is >= p_{jn}
        if f < hi and f <= lim: hits.append((j, f // n))
        else:
            miss = f - hi + 1                        # how far the multiple lies beyond the interval
            if f <= lim and (best is None or miss < best[0]): best = (miss, j, lo, hi, f // n)
        cnt += 1; j += W
        if cnt % 5000 == 0:
            with open(f'verify_{n}_{r}.progress', 'w') as g: g.write(f'{cnt} j={j} {time.time()-t0:.0f}s\n')
    with open(f'verify_{n}_{r}.txt', 'w') as g:
        g.write(f'n={n} p_n={p} worker={r}/{W} checked={cnt} last_j={j - W} hits={hits} closest={best} seconds={time.time()-t0:.0f}\n')
if __name__ == '__main__':
    ps = [Process(target=work, args=(r,)) for r in range(W)]
    [q.start() for q in ps]; [q.join() for q in ps]
    for r in range(W): print(open(f'verify_{n}_{r}.txt').read().strip())
