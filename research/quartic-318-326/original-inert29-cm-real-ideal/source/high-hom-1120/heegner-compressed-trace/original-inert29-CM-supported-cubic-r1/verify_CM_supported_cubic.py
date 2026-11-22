#!/usr/bin/env python3
"""Exact symmetric T5 function and CM-supported cubic readout on fixed inert-29 flags."""
import json,math,sys
from pathlib import Path
from itertools import combinations_with_replacement
from fractions import Fraction as F
from hashlib import sha256
root=Path(__file__).resolve().parent.parents[2]
src=root/'high-hom-1120/heegner-compressed-trace/original-detectors-inert29-finite-receiver-r1/replay_inert29.py'
assert sha256(src.read_bytes()).hexdigest()=='e1f570297815f21b270374b01a5f0972ee0d1cb20f7123082de254e4318d08f5'
sys.path.insert(0,str(src.parent))
import replay_inert29 as m

# Laurent q-expansion on X_0(48), pullback of rank-six Riemann--Roch basis.
L=250
def mul(a,b,T=None):
    r={}
    for i,v in a.items():
        for j,w in b.items():
            if T is None or i+j<=T:r[i+j]=r.get(i+j,0)+v*w
    return {i:v for i,v in r.items() if v}
def scale(a,k,shift=0):return {i+shift:v*k for i,v in a.items() if k}
def add(a,b):
    c=a.copy()
    for i,v in b.items():c[i]=c.get(i,0)+v
    return {i:v for i,v in c.items() if v}
ds={4:1,16:2,24:3,8:-3,12:-1,48:-2}
A={0:1}
for a,e in ds.items():
    for i in range(a,L+1,a):
        b={j*i:(-1)**j*math.comb(e,j) if e>0 else math.comb(-e+j-1,j)
            for j in range((min(e,L//i) if e>0 else L//i)+1)}
        A=mul(A,b,L)
assert A[0]==1
Am={0:1}
for n in range(1,L+1):Am[n]=-sum(A.get(i,0)*Am[n-i] for i in range(1,n+1))
Am={i:v for i,v in Am.items() if v}
XP={0:{0:1},1:scale(A,1,-1),-1:scale(Am,1,1)}
def pX(k):
    if k not in XP:
        XP[k]=mul(XP[1 if k>0 else -1],pX(k-1 if k>0 else k+1),L+8)
    return XP[k]
# Y=X^4 sqrt(1+14/X^4+1/X^8). Integral coefficients verified.
ser={}
for n in range(1+L//4):
    cc=(14 if n==1 else 1 if n in (0,2) else 0)
    ser[n]=1 if n==0 else F(cc-sum(ser[j]*ser[n-j] for j in range(1,n)),2)
assert all(k.denominator==1 for k in map(F,ser.values()))
B=[{0:1}]
for k in range(5):
    c={}
    for j,s in ser.items():
        e=4+k-4*j
        if e>L:continue
        s*=2 if e>0 else 1
        c=add(c,scale(pX(e),s))
    B.append({i:v for i,v in c.items() if i<=180})
assert [(min(b),b[min(b)]) for b in B]==[(0,1),(-4,2),(-5,2),(-6,2),(-7,2),(-8,2)]
T=125;D=[]
IJ=list(combinations_with_replacement(range(6),2))
for i,j in IJ:
    G=mul(B[i],{5*k:v for k,v in B[j].items()},T)
    H=mul(B[i],B[j],T)
    if i!=j:
        G=add(G,mul(B[j],{5*k:v for k,v in B[i].items()},T));H=scale(H,2)
    D.append((G,H))
c0={(0,0):2,(0,5):2,(1,1):-2,(2,4):-1,(3,3):2}
CO=[c0.get(ij,0) for ij in IJ]
assert all(sum(co*d[k].get(i,0) for co,d in zip(CO,D))==0
           for i in range(-48,115) for k in (0,1))
# On affine curve, y is short Y, not y48. Use old fixed phase.
def vals(X,Y):
    Z=m.add(Y,m.pw(X,4))
    return [1,Z,*[m.mul(m.pw(X,k),m.add(Z,7)) for k in range(1,5)]]
gamma=m.f(14,5); cube={m.pw(gamma,i):i for i in range(3)}
ref=root/'rc-native-helper-20261120/ct-level48-fixed103-inert29-tate-cubic-r1/EXACT-INERT29-TATE-CUBIC.json'
assert sha256(ref.read_bytes()).hexdigest()=='57c008b35c79fb8cf35ba5c77dd444b021120151a73dbaaace80b009a3631a7f'
rows=json.loads(ref.read_text())['all_flags']
M=[[0]*6 for _ in range(6)]
for (i,j),a in zip(IJ,CO):M[i][j]=M[j][i]=a%29
gweights=[]
for X,Y,*_,u,k in rows:
    v=vals(X,Y)
    w=[]
    for i in range(6):
       x=0
       for j in range(6):x=m.add(x,m.mul(M[i][j],v[j]))
       w.append(x)
    A=m.phi(X,Y); H=m.pm(4,m.p_add(A,m.p_neg(m.p_fr(A))))
    j=next(j for j in range(9) if m.pm(j,(14,m.f(0,13)))==H)
    assert j%3==k
    gweights.append((w,k))

def evalc(P,w): 
    r=0
    for x,y in zip(P,w):
        r=m.add(r,m.mul(x,y))
    assert r
    return cube[m.pw(r,560)]

T=m.roots_table()
C=list(m.curvepoints(T));SS={(X,Y) for X,Y,*_ in rows}
O=[Q for Q in C if m.j48(*Q) not in (None,0,2,25)]
assert all(all(q is not None for q in Q) for Q in O)
assert len(SS)==224 and len(O)==672 and not any(all(x<29 for x in P) for P in O)
assert SS=={Q for Q in C if m.j48(*Q) in (0,2,25)}
idx={(v[0],v[1]):i for i,v in enumerate(rows)}
flags=list(idx)
def w3(Q):
    X,Y=Q
    return m.div(28,X),m.div(m.neg(Y),m.pw(X,4))
def w16(Q):return m.w48(*w3(Q))
def ab(Q):
    return Q,w16(Q),w3(Q),m.w48(*Q)
sign=(1,1,-1,-1)
idxs=[tuple(idx[q] for q in ab(P)) for P in flags]
assert all([gweights[i][1] for i in row]==[(x*gweights[row[0]][1])%3 for x in sign] for row in idxs)
assert all((gweights[idx[m.q_fr(*P)]][1]+gweights[idx[P]][1])%3==0 for P in flags)
def vec(Q):
    P=vals(*Q);PF=vals(*m.q_fr(*Q))
    v=[(evalc(P,w)+evalc(PF,w))%3 for w,_ in gweights]
    return [sum(x*v[i] for i,x in zip(row,sign))%3 for row in idxs]
W={
 (65,660):1,(147,317):-1,(159,256):-1,(191,789):-1,(192,723):1,
 (253,274):1,(324,526):-1,(367,497):1,(393,327):1,
}
O2={Q for Q in O if Q<m.q_fr(*Q)}
assert set(W)<=O2 and len(O2)==336
target=[k for _,k in gweights]
observed=[0]*len(flags)
piv={}
for Q in sorted(O2):
    v=vec(Q)
    if Q in W:observed=[(x+W[Q]*y)%3 for x,y in zip(observed,v)]
    for i,a in sorted(piv.items()):
        r=v[i]
        if r:v=[(x-r*y)%3 for x,y in zip(v,a)]
    if any(v):
        i=next(i for i,x in enumerate(v) if x)
        piv[i]=[(v[i]*x)%3 for x in v]
assert observed==target and len(piv)==25
print(json.dumps(dict(
   scope='Exact fixed-chart CM-supported cubic readout; no moving norm or point.',
   q_exponents_checked=[-48,114],rr_bidegree=[8,8],ordinary_rows=len(O),
   supersingular_flags=len(flags),projected_rank=len(piv),projected_terms=len(W),
   symmetric_coefficients=[[i,j,c] for (i,j),c in sorted(c0.items())],
   signed_ordinary_rows=[[X,Y,W[X,Y]] for X,Y in sorted(W)],
   ordered_cubic_bit_sha256=sha256(bytes(target)).hexdigest(),
),sort_keys=True,indent=2))
