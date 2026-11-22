# Sun's Conjecture 4.6 for all n <= N, with partition numbers from FLINT (python-flint).
#   T = { m <= N : m-1, m+1 and q(m)+1 all prime }   (OEIS A235344)
#   a(n) = #{ 0 < k < n : phi(k) + phi(n-k)/4 in T }  (OEIS A235343)
# q(m) comes from Gauss's identity q(m) = sum p((m - t)/2) over triangular t <= m, t = m (mod 2).
# Usage: python3 extend46.py N [workers] [ii]
# With "ii" it tests part (ii) of the conjecture in A235343 instead: for n > 1234 some k has
# m = phi(k) + phi(n-k)/8 with m-1, m+1 and q(m)-1 all prime (those m are OEIS A235346).
import sys, time, pickle, numpy as np
from multiprocessing import Pool
from gmpy2 import mpz, is_prime, gcd, primorial
N=int(sys.argv[1]); WORKERS=int(sys.argv[2]) if len(sys.argv)>2 else 3
PART2=len(sys.argv)>3 and sys.argv[3]=='ii'
SIGN,DIV,N0,TAG=(-1,8,1235,'ii_') if PART2 else (1,4,60,'')
H=N//2
def chunk(r):
    from flint import fmpz
    a,b=r
    return a,[int(fmpz(i).partitions_p()) for i in range(a,b)]
def main():
    t0=time.time()
    step=5000; rs=[(a,min(a+step,H+1)) for a in range(0,H+1,step)]
    P=[None]*(H+1)
    with Pool(WORKERS) as pool:
        for i,(a,vals) in enumerate(pool.imap_unordered(chunk,rs,chunksize=1)):
            P[a:a+len(vals)]=vals
            if i%100==0: print(f'partition table chunk {i}/{len(rs)} [{time.time()-t0:.0f}s]',flush=True)
    print('partition table done',H,f'[{time.time()-t0:.0f}s]',flush=True)
    M=N+2
    isp=np.ones(M+1,dtype=bool); isp[:2]=False
    for i in range(2,int(M**0.5)+1):
        if isp[i]: isp[i*i::i]=False
    PRIM=primorial(200000)
    T=[]; ntw=0
    for m in range(4,N+1,2):
        if isp[m-1] and isp[m+1]:
            ntw+=1
            s=0; j=0; t=0
            while t<=m:
                if (m-t)%2==0: s+=P[(m-t)//2]
                j+=1; t=j*(j+1)//2
            x=mpz(s+SIGN)
            if x<10**9: ok=bool(is_prime(x,25))
            else: ok=(gcd(x,PRIM)==1) and bool(is_prime(x,8))
            if ok:
                T.append(m); print('T element',m,'digits',len(str(s+SIGN)),f'[{time.time()-t0:.0f}s]',flush=True)
    print('twin centres',ntw,' |T| =',len(T),f'[{time.time()-t0:.0f}s]',flush=True)
    del P
    pickle.dump(T,open(f'T46_{TAG}{N}.pkl','wb'))
    phi=np.arange(N+1,dtype=np.int64)
    for i in range(2,N+1):
        if isp[i]: phi[i::i]-=phi[i::i]//i
    ks=np.arange(1,N+1); v=phi[1:]
    o=np.argsort(v,kind='stable'); ks=ks[o]; vs=v[o]
    start=np.searchsorted(vs,np.arange(N+2))
    js_all=np.arange(1,N+1); ok=(phi[1:]%DIV==0); js_all=js_all[ok]; Bj=phi[1:][ok]//DIV
    cnt=np.zeros(N+1,dtype=np.int32)
    for t in T:
        vv=t-Bj; okv=(vv>=1)
        js=js_all[okv]; vv=vv[okv]
        c=start[vv+1]-start[vv]; nz=c>0; js=js[nz]; vv=vv[nz]; c=c[nz]
        if len(js)==0: continue
        jrep=np.repeat(js,c); base=np.repeat(start[vv],c)
        within=np.arange(len(jrep))-np.repeat(np.cumsum(c)-c,c)
        n=ks[base+within]+jrep
        cnt+=np.bincount(n[n<=N],minlength=N+1).astype(np.int32)
    z=np.nonzero(cnt[N0:]==0)[0]+N0
    print('T =',T)
    print(f'n in [{N0},{N}] with a(n) = 0:',z.tolist())
    one=np.nonzero(cnt[N0:]==1)[0]+N0
    print('number of n with a(n) = 1:',len(one),' largest few:',one[-8:].tolist())
    np.save(f'a46_{TAG}{N}.npy',cnt)
    print('done',f'[{time.time()-t0:.0f}s]')
if __name__=='__main__': main()
