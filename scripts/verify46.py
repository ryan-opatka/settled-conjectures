# Independent brute-force check of Sun's Conjecture 4.6 (arXiv:1402.6641) at a given n.
# Uses none of the tables from big.py: totients and primality from sympy, partition numbers from
# sympy's Hardy-Ramanujan-Rademacher implementation, and q(m) from Gauss's identity
#     q(m) = sum_{j>=0, T_j<=m, T_j = m (mod 2)} p((m - T_j)/2),   T_j = j(j+1)/2.
import sys, time, json
from fractions import Fraction
from sympy import totient, isprime, npartitions
from gmpy2 import mpz, powmod, gcd, primorial, is_prime
n=int(sys.argv[1])
t0=time.time()
ms={}          # m -> list of k
nonint=0
for k in range(1,n):
    m=Fraction(int(totient(k)))+Fraction(int(totient(n-k)),4)
    if m.denominator!=1: nonint+=1; continue
    m=int(m)
    if isprime(m-1) and isprime(m+1):
        ms.setdefault(m,[]).append(k)
print(f'n={n}: k in 1..{n-1}; non-integer m for {nonint} values of k; distinct integer m with m-1 and m+1 both prime: {len(ms)}  (min {min(ms)}, max {max(ms)})  [{time.time()-t0:.0f}s]',flush=True)
pc={}
def P(i):
    if i not in pc: pc[i]=mpz(int(npartitions(i)))
    return pc[i]
def q(m):
    s=mpz(0); j=0
    while j*(j+1)//2<=m:
        T=j*(j+1)//2
        if (m-T)%2==0: s+=P((m-T)//2)
        j+=1
    return s
assert [int(q(i)) for i in range(1,13)]==[1,1,2,2,3,4,5,6,8,10,12,15]
PRIM=primorial(100000)
wit=[]; cert={}
for m in sorted(ms):
    N=q(m)+1
    g=gcd(N,PRIM)
    if g!=1 and g!=N:
        # explicit small prime factor
        f=int(min(pp for pp in range(2,100000) if g%pp==0)) if g<10**12 else None
        if f is None:
            import sympy; f=min(sympy.primefactors(int(g)))
        assert N%f==0 and 1<f<N
        cert[m]=('factor',f)
    elif powmod(2,N-1,N)!=1:
        cert[m]=('fermat base 2 fails',None)
    elif powmod(3,N-1,N)!=1:
        cert[m]=('fermat base 3 fails',None)
    else:
        wit.append(m); cert[m]=('PROBABLE PRIME',bool(is_prime(N,30)))
print(f'partition values used: {len(pc)}; [{time.time()-t0:.0f}s]')
kinds={}
for m,(c,_) in cert.items(): kinds[c]=kinds.get(c,0)+1
print('certificates for q(m)+1:',kinds)
if wit:
    print('WITNESSES (m with m-1, m+1, q(m)+1 all prime):',[(m,ms[m][:3],cert[m]) for m in wit])
else:
    print(f'NO WITNESS: for every k in 1..{n-1} with m=phi(k)+phi(n-k)/4 an integer and m-1, m+1 prime, q(m)+1 is composite.')
json.dump({'n':n,'m_values':{str(m):{'k':ms[m],'cert':cert[m][0],'factor':cert[m][1]} for m in sorted(ms)}},open(f'verify46_{n}.json','w'))
