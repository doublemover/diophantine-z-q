#!/usr/bin/env python3
import json,random

def zmat(n): return [[0]*n for _ in range(n)]
def rank(M):
    B={}
    for rr in M:
        v=sum((a&1)<<i for i,a in enumerate(rr))
        while v:
            k=v.bit_length()-1
            if k not in B:
                B[k]=v;break
            v^=B[k]
    return len(B)
def sub(M,I):return [[M[i][j] for j in I] for i in I]
def lap(A):
    L=[r[:] for r in A]
    for i,r in enumerate(L):r[i]=sum(r)%2
    return L
def add(A,u,v,a,p):
    A[u][v]=a
    A[v][u]=a^(p[u]*p[v])

r=random.Random(17)
rows=0;directed=0;nonzero_17=0;nonzero_3=0
# Fixed base is the tree case of the first construction, with:
# 0=17, 1..6=genuine contacts, 7=special helper r0, 8=q0.
for k in range(13):
    for _ in range(90):
        A=zmat(9+2*k); pos=[0]*len(A); pos[8]=1
        ts=list(range(9,9+k));rs=list(range(9+k,9+2*k))
        tv=[r.randrange(2) for _ in ts]
        if k:tv[-1]=sum(tv[:-1])%2
        for t,a in zip(ts,tv):pos[t]=a
        for a,b in zip(range(1,6),range(2,7)):add(A,a,b,1,pos)
        for v in (7,8):
            for i in (0,1):add(A,i,v,1,pos)
        add(A,7,8,1,pos)
        # Rows and columns of old-beta/theta coupling have even sum;
        # generate them by 2x2 toggles, including arbitrary 17 incidences.
        if k>=2:
            for a in range(6):
                for j in range(k-1):
                    if r.randrange(2):
                        for i in (a,6):
                            for t in (ts[j],ts[-1]):add(A,i,t,A[i][t]^1,pos)
        for i,t in enumerate(ts):
            for u in ts[i+1:]:add(A,t,u,r.randrange(2),pos)
            add(A,8,t,r.randrange(2),pos)
        for t,v in zip(ts,rs):
            add(A,8,v,1,pos);add(A,t,v,1,pos)
        lam=[0]*len(A);lam[0]=lam[8]=1
        lv=[r.randrange(2) for _ in ts]
        if k:lv[-1]=sum(lv[:-1])%2
        for t,a in zip(ts,lv):lam[t]=a
        directed+=any(A[t][u]!=A[u][t] for t in ts for u in ts)
        nonzero_17+=any(A[t][0] for t in ts)
        nonzero_3+=any(lam[t] for t in ts)
        for use in (list(range(9))+rs,list(range(9))+ts+rs):
            L=lap(sub(A,use));ix=use.index(8)
            assert all(sum(rr[:7])%2==0 for rr in L)
            for j,u in enumerate(use):
                L[j][0]^=lam[u];L[j][ix]^=lam[u]
            C=sub(L,[i for i,u in enumerate(use) if u!=8])
            use2=[u for u in use if u!=0]
            B=sub(lap(sub(A,use2)),[i for i,u in enumerate(use2) if u!=8])
            assert rank(C)==len(C) and rank(B)==len(B)
            rows+=1
assert min(directed,nonzero_17,nonzero_3)>0
print(json.dumps(dict(two_gate_replays=rows,theta_roster_sizes=list(range(13)),
                      directed_theta_examples=directed,
                      physical_17_edges_examples=nonzero_17,
                      nonzero_3_symbol_examples=nonzero_3),indent=2,sort_keys=True))
