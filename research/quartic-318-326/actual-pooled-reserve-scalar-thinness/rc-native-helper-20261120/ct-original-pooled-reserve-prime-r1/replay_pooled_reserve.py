"""Literal Jacobi matrices with genuinely asymmetric theta block; no rank scan."""
from math import isqrt, prod
import json

def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))
def bit(u,v):
    assert u % v
    return int(pow(u,(v-1)//2,v)==v-1)
def parity(l):
    return sum(l)%2
def dot(u,v):
    return parity([i*j for i,j in zip(u,v)])
def rank(A):
    A=[r[:] for r in A]
    k=0
    for j in range(len(A[0])):
        p=next((i for i in range(k,len(A)) if A[i][j]),None)
        if p is None: continue
        A[k],A[p]=A[p],A[k]
        for i in range(k+1,len(A)):
            if A[i][j]: A[i]=[u^v for u,v in zip(A[i],A[k])]
        k+=1
    return k
def solve(A,b):
    n=len(A)
    assert rank(A)==n
    return next(v for j in range(1<<n) if [dot(row,v:=[(j>>i)&1 for i in range(n)]) for row in A]==b)
def mm(A,B):
    return [[dot(a,b) for b in zip(*B)] for a in A]
def sharp(P):
    assert all(prime(p) for p in P) and len(set(P))==len(P)
    assert P[-1]%12==7 and prod(P)%12==11
    L=[]
    for i,u in enumerate(P):
        row=[0 if u==v else bit(v,u) for v in P]
        row[i]=parity(row)
        L.append(row)
    assert all(not parity(row[:2]) for row in L)
    return [[b ^ (bit(3,P[i]) if j==0 else 0)
             for j,b in enumerate(row[:-1])] for i,row in enumerate(L[:-1])]

B=[17,73]
J=[139,163]
q0=67
R=[337,1213]
C=sharp(B+[q0])
F=sharp(B+J+[q0])
Y=[r[:len(B)] for r in F[len(B):]]
assert not any(parity(c) for c in zip(*Y))
assert [r[:len(B)] for r in F[:len(B)]]==C
assert any(F[i][j]!=F[j][i] for i in range(len(F)) for j in range(len(F)))
assert rank(C)==len(B) and rank(F)==len(B)+len(J)
assert prod(B)%24==17 and prod(J)%24==1
W=[]
V=[]
for r in R:
    assert r%12==1
    v=[bit(r,p) for p in B]; w=[bit(r,p) for p in J]
    x=solve(C,v)
    assert not parity(v)
    assert w==[dot(y,x) for y in Y]
    assert solve(F,v+w)==x+[0]*len(J)
    assert w!=[0]*len(J)
    assert bit(r,q0)==1^parity(v)
    V.append(v); W.append(w)
assert not any(parity(c) for c in zip(*V))
assert not any(parity(c) for c in zip(*W))
controls=[]
for s in (5557,1237,733,2269):
    assert s%12==1 and [bit(s,p) for p in B+J+[q0]]==[0,0,0,0,1]
    new=R+[s]
    small=sharp(B+new+[q0]); full=sharp(B+J+new+[q0])
    assert [row[:len(B)] for row in small[:len(B)]]==C
    assert [row[:len(F)] for row in full[:len(F)]]==F
    S=[]
    for A,n in ((small,len(B)),(full,len(F))):
        old=[row[:n] for row in A[:n]]
        up=[row[n:] for row in A[:n]]
        lo=[row[:n] for row in A[n:]]
        D=[row[n:] for row in A[n:]]
        solved=list(zip(*(solve(old,list(col)) for col in zip(*up))))
        corr=mm(lo,solved)
        S.append([[x^y for x,y in zip(a,b)] for a,b in zip(D,corr)])
    assert S[0]==S[1] and all(parity(r) for r in S[0]) and all(parity(c) for c in zip(*S[0]))
    rS=rank(S[0])
    assert rank(small)==len(B)+rS and rank(full)==len(F)+rS
    controls.append(dict(reserve=s,reserve_bits=[bit(s,p) for p in R],common_Schur=S[0],ranks=[rank(small),rank(full)]))
assert [d['ranks'] for d in controls]==[[5,7],[5,7],[5,7],[4,6]]
print(json.dumps(dict(scope='actual prime-data Schur and selection control, not an original literal pole or rank',
                      beta_primes=B,theta_primes=J,fixed_q0=q0,old_small=C,old_companion=F,
                      small_new_primes=R,base_incidence=V,theta_incidence=W,rows=controls),
                 indent=2,sort_keys=True))
