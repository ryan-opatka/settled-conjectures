# Witness sets for Sun's conjectures 4.3(ii), 4.6, 4.7(i), 4.8(i) up to N (arXiv:1402.6641): exact p(n), q(n) by pentagonal recurrences
import sys, time, pickle, numpy as np
from gmpy2 import mpz, is_prime, gcd, primorial
N = int(sys.argv[1])
t0=time.time()
def pentlist(mult):
    out=[]; k=1
    while True:
        a=mult*k*(3*k-1)//2; b=mult*k*(3*k+1)//2
        if a>N: break
        out.append((a, k%2==1))
        if b<=N: out.append((b, k%2==1))
        k+=1
    return out
pent=pentlist(1)
p=[mpz(0)]*(N+1); p[0]=mpz(1)
for n in range(1,N+1):
    s=mpz(0)
    for g,odd in pent:
        if g>n: break
        if odd: s+=p[n-g]
        else: s-=p[n-g]
    p[n]=s
    if n%100000==0: print('p',n,time.time()-t0,flush=True)
assert p[100]==190569292 and p[1000]==mpz('24061467864032622473692149727991')
pent2=pentlist(2)
M=N+2
isp=np.ones(M+1,dtype=bool); isp[:2]=False
for i in range(2,int(M**0.5)+1):
    if isp[i]: isp[i*i::i]=False
PRIM=primorial(20000)
def PR(x):
    if x<4: return x in (2,3)
    if x<400000000:
        return is_prime(x,12)
    if gcd(x,PRIM)!=1: return False
    return is_prime(x,6)
S43ii=[]; T46=[]; R47i=[]; Q48i=[]
for n in range(1,N+1):
    need_q = (isp[n-1] and isp[n+1]) or isp[n]
    if isp[n+1] and PR(p[n]): S43ii.append(n)
    if need_q:
        s=p[n]
        for g,odd in pent2:
            if g>n: break
            if odd: s-=p[n-g]
            else: s+=p[n-g]
        qn=s
        if isp[n-1] and isp[n+1] and PR(qn+1): T46.append(n)
        if isp[n]:
            if PR(p[n]+qn): R47i.append(n)
            if PR(p[n]-qn): Q48i.append(n)
    if n%100000==0: print('sets',n,len(S43ii),len(T46),len(R47i),len(Q48i),time.time()-t0,flush=True)
pickle.dump({'S43ii':S43ii,'T46':T46,'R47i':R47i,'Q48i':Q48i},open(f'thin_{N}.pkl','wb'))
print('S43ii',S43ii); print('T46',T46); print('R47i',R47i); print('Q48i',Q48i)
print('done',time.time()-t0)
