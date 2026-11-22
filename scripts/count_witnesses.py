# Exact witness counts for Sun's Conj. 4.3(ii), 4.6, 4.7(i), 4.8(i) for all n<=N.
import sys, time, pickle, numpy as np
N=int(sys.argv[1]); src=sys.argv[2]
sets=pickle.load(open(src,'rb'))
M=N+2
phi=np.arange(M+1,dtype=np.int64)
for i in range(2,M+1):
    if phi[i]==i: phi[i::i]-=phi[i::i]//i
phi=phi[:N+1]
def inv_csr(vals, maxv):
    ks=np.arange(1,N+1); v=vals[1:N+1]
    ok=(v>=0)&(v<=maxv); ks=ks[ok]; v=v[ok]
    o=np.argsort(v,kind='stable'); ks=ks[o]; v=v[o]
    return ks, np.searchsorted(v, np.arange(maxv+2))
def count(S, A, B, jmin, off=0):
    cnt=np.zeros(N+1,dtype=np.int64)
    S=[t for t in S if t<=N+off]
    maxv=max(S)
    ks,start=inv_csr(A,maxv)
    js_all=np.arange(jmin,N+1); Bj_all=B[jmin:N+1]
    ok=Bj_all>=0; js_all=js_all[ok]; Bj_all=Bj_all[ok]
    for t in S:
        v=t-off-Bj_all
        okv=(v>=0)&(v<=maxv); js=js_all[okv]; v=v[okv]
        c=start[v+1]-start[v]; nz=c>0; js=js[nz]; v=v[nz]; c=c[nz]
        if len(js)==0: continue
        jrep=np.repeat(js,c); base=np.repeat(start[v],c)
        within=np.arange(len(jrep))-np.repeat(np.cumsum(c)-c,c)
        n=ks[base+within]+jrep
        cnt+=np.bincount(n[n<=N],minlength=N+1)
    return cnt
def div(a,c):
    r=np.where(a%c==0,a//c,-1); r[0]=-1; return r
PH=phi.copy(); PH[0]=-1
out={}
# 4.3(ii): k<n-2 (j>=3), t=phi(k)+phi(j)/2 in S43ii
out['4.3(ii)']=(count(sets['S43ii'],PH,div(phi,2),3,0),728,56000)
# 4.6: t=phi(k)+phi(j)/4 in T46
out['4.6']=(count(sets['T46'],PH,div(phi,4),1,0),60,100000)
# 4.7(i): r=phi(k)+phi(j)/6+1 in R47i
out['4.7(i)']=(count(sets['R47i'],PH,div(phi,6),1,1),128,30000)
# 4.8(i): p=(6phi(k)+phi(j))/12+1 in Q48i ; k>=3: 12|phi(j); k in {1,2}: phi(j)=6 mod 12
A=div(phi,2); A[1]=-1; A[2]=-1
c=count(sets['Q48i'],A,div(phi,12),1,1)
Q=set(sets['Q48i'])
extra=np.zeros(N+1,dtype=np.int64)
for kk in (1,2):
    for n in range(kk+1,N+1):
        f=int(phi[n-kk])
        if f%12==6 and ((6+f)//12+1) in Q: extra[n]+=1
print('4.8(i): n with extra witnesses from k in {1,2}:',int((extra>0).sum()))
out['4.8(i)']=(c+extra,99,None)
for name,(cnt,thr,ver) in out.items():
    fails=np.nonzero(cnt[1:]==0)[0]+1
    fa=fails[fails>=thr]
    print(f'== Conj {name}  [Sun verified to {ver}]')
    print('   last failures below threshold:', fails[fails<thr][-6:].tolist())
    print('   FAILURES at n>=threshold:', fa[:60].tolist(), ' total', len(fa))
    edges=[thr,1000,10000,30000,100000,200000,300000,500000,700000,1000000,2000000,3000000,5000000,10000000]
    for lo,hi in zip(edges,edges[1:]):
        if hi<=N:
            seg=cnt[lo:hi+1]
            print(f'   n in [{lo},{hi}]: zeros {int((seg==0).sum())}, min {int(seg.min())} (n={lo+int(seg.argmin())}), #count<=2: {int((seg<=2).sum())}, median {int(np.median(seg))}')
pickle.dump({k:v[0] for k,v in out.items()},open(f'reps2_{N}.pkl','wb'))
