# Compares the output of extend46.py with Sun's own tables in the OEIS:
#   b235343.txt  a(n) for n = 1..10000   (A235343, the number of suitable k)
#   b235344.txt  the first 51 numbers m with m-1, m+1 and q(m)+1 all prime   (A235344)
# Usage: python3 compare_oeis.py a46_N.npy T46_N.pkl      (needs N >= 3235368 for the second)
import sys, pickle, urllib.request, numpy as np

def bfile(name):
    url = f'https://oeis.org/A{name[1:7]}/{name}'
    req = urllib.request.Request(url, headers={'User-Agent': 'compare_oeis.py'})  # the default is refused
    text = urllib.request.urlopen(req, timeout=60).read().decode()
    return [tuple(map(int, l.split()[:2])) for l in text.splitlines() if l.strip() and l[0] != '#']

a = np.load(sys.argv[1], mmap_mode='r')
T = sorted(pickle.load(open(sys.argv[2], 'rb')))
b = bfile('b235343.txt')
bad = [(n, v, int(a[n])) for n, v in b if int(a[n]) != v]
print(f'A235343: {len(b)} terms (n = {b[0][0]}..{b[-1][0]}), {len(bad)} mismatches', bad[:5])
t = [v for _, v in bfile('b235344.txt')]
mine = [m for m in T if m <= t[-1]]
print(f'A235344: {len(t)} terms (up to {t[-1]}),', 'identical' if mine == t else 'DIFFERENT')
sys.exit(1 if bad or mine != t else 0)
