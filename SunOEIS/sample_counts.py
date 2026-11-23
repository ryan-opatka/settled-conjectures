# Full counts a(n) for a sample of n, to see whether the number of solutions is still flat far past Sun's tables.
import sys, random, time
import e1scan
from multiprocessing import Pool
name = sys.argv[1]; lo, hi, k = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
random.seed(5); ns = sorted(random.sample(range(lo, hi), k))
def work(n): return n, e1scan.count(n)
if __name__ == '__main__':
    t0 = time.time()
    c = []
    with Pool(4, initializer=e1scan.init, initargs=(name, hi)) as pool:
        for n, x in pool.imap_unordered(work, ns, chunksize=1):
            c.append(x); print(f'  a({n}) = {x} [{time.time()-t0:.0f}s]', flush=True)
    print(f'{name}: {k} values of n in [{lo},{hi}): mean a(n) = {sum(c)/len(c):.1f}, min {min(c)}, max {max(c)}, values {sorted(c)} [{time.time()-t0:.0f}s]')
