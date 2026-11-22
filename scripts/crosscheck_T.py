# Independent recomputation of T = {m <= N : m-1, m+1, q(m)+1 all prime} using sympy's
# Rademacher-type partition function and Gauss's identity; compared with the list from big.py.
import sys, pickle, time, warnings
warnings.filterwarnings('ignore')
from multiprocessing import Pool
from sympy import isprime
from sympy.functions.combinatorial.numbers import partition
from gmpy2 import mpz, is_prime
N=int(sys.argv[1]); H=N//2
def chunk(r):
    a,b=r
    return a,[int(partition(i)) for i in range(a,b)]
if __name__=='__main__':
    t0=time.time()
    step=2000; rs=[(a,min(a+step,H+1)) for a in range(0,H+1,step)]
    P=[None]*(H+1)
    with Pool(4) as pool:
        for a,vals in pool.imap_unordered(chunk,rs):
            P[a:a+len(vals)]=vals
    print('partition table',H,time.time()-t0,flush=True)
    P=[mpz(x) for x in P]
    T=[]
    for m in range(2,N+1):
        if isprime(m-1) and isprime(m+1):
            s=mpz(0); j=0
            while True:
                t=j*(j+1)//2
                if t>m: break
                if (m-t)%2==0: s+=P[(m-t)//2]
                j+=1
            if is_prime(s+1,10): T.append(m)
    print('T recomputed:',len(T),time.time()-t0)
    ref=pickle.load(open(f'thin_{N}.pkl','rb'))['T46']
    print('agrees with big.py list:',T==ref)
    if T!=ref: print(sorted(set(T)^set(ref)))
