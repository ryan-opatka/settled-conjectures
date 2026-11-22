# Runs verify46.gp through the PARI library (pip install cypari), for machines without gp.
# Usage: python3 run_gp.py [n ...]      (default: 59 60 267496 267497 267498)
# With --prove it also proves, with PARI's isprime, that q(m) + 1 is prime for every m < 267497
# in the list T of certificate_267497.json (so that 267497 is the smallest counterexample).
import sys, re, time, json, os
from cypari import pari
pari.allocatemem(2 * 10**9)
src = open(os.path.join(os.path.dirname(__file__), 'verify46.gp')).read()
src = '\n'.join(l for l in src.splitlines() if not l.lstrip().startswith('\\\\'))
for chunk in src.split('};'):
    chunk = chunk.strip()
    if not chunk: continue
    head, body = chunk.split('{', 1)
    pari(head.strip() + ' ' + ' '.join(body.split()))
args = [a for a in sys.argv[1:] if a != '--prove']
ns = [int(a) for a in args] or [59, 60, 267496, 267497, 267498]
assert [int(pari(f'q({i})')) for i in range(1, 13)] == [1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15]
for n in ns:
    t0 = time.time()
    r = pari(f'check({n})')
    wit = sorted(set(int(x[1]) for x in r[3]))
    print(f'n = {n}: {int(r[0])} values of k with m integral and m-1, m+1 prime ({int(r[1])} distinct m); '
          f'q(m)+1 fails Fermat base 2 for {int(r[2])} of them; '
          + (f'NO k works' if not wit else f'{len(r[3])} k work, with m in {wit}') + f'  [{time.time()-t0:.0f}s]', flush=True)
if '--prove' in sys.argv:
    T = json.load(open(os.path.join(os.path.dirname(__file__), 'certificate_267497.json')))['all_m_up_to_1e6_with_m-1_m+1_q(m)+1_prime']
    for m in [t for t in T if t < 267497]:
        t0 = time.time()
        ok = int(pari(f'isprime(q({m})+1)'))
        print(f'm = {m}: q(m)+1 has {len(str(pari(f"q({m})+1")))} digits, isprime = {ok}  [{time.time()-t0:.0f}s]', flush=True)
        assert ok == 1
    print('all proved prime')
