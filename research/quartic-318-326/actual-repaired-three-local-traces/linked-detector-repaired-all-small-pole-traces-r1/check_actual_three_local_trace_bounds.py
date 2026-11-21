#!/usr/bin/env python3
"""Exact inert p=3 residue donor and same-index all-small pole exponent checks."""
from pathlib import Path
from hashlib import sha256
P=Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py'
raw=P.read_bytes()
assert sha256(raw).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(raw.decode().split('\nqs=(')[0],globals())
S=P.parent.parent/'linked-detector-numeric-anchor-phase-repair-r1/EXACT-PRIMARY-REPAIRED-COVER.json'
data=json.loads(S.read_bytes())
h=int(data['final_h']); a,b=[int(data[j]) for j in ('a','b')]
assert h%20==0 and vp(h,3)>=4 and h%64==0 and vp(h,17)==1
assert labels(2)==(1,1,1,1)
assert a%8==b%8==1 and chi(a,3)==chi(b,3)==chi(a,17)==chi(b,17)==1
p=3;M=9;o,P,U,formal=F0(p,None);m=o();ls=labels(m*p)
assert m==4 and formal(P(m)) and P(m)==(6,3)
def mul(a,b):return ((a[0]*b[0]+2*a[1]*b[1])%M,(a[0]*b[1]+a[1]*b[0])%M)
def add(a,b):return ((a[0]+b[0])%M,(a[1]+b[1])%M)
def sc(a,k):return (a[0]*k%M,a[1]*k%M)
def nr(x):return (x[0]**2-2*x[1]**2)%M
def inv(x):return sc((x[0],-x[1]),pow(nr(x),-1,M))
K=(11%M,-6%M);G=(1,0);opp=[]
for n in ls:
 Q=P(n);xx,y=Q
 x2=mul(xx,xx);s2=add(x2,K); ar=U(Q)
 assert nr(ar)%3 and nr(s2)%3
 G=mul(G,sc(inv(ar),-1))
 V=mul(add(add(mul(x2,x2),sc(mul(K,x2),-6)),mul(K,K)),inv(mul(s2,s2)))
 qJ=add((1,0),sc(add(V,(-1,0)),5*pow(13,-1,M)))
 assert nr(qJ)%3
 opp.append(dict(U=ar,V=V,QJ=qJ))
C=[1,(G[0]+nr(G))%M,nr(G)]
assert C==[1,6,4]
k=(-1%M,(7*pow(4,-1,M))%M)
m=(39*pow(8,-1,M)%M,-9*pow(2,-1,M)%M)
arg=mul(K,inv(mul(mul(k,k),mul(k,k))))
assert nr(k)%3 and nr(K)%3 and min(vp(z,3) for z in m)==1
assert [z%3 for z in arg]==[1,0]
rows=[]
for p,mW,Cp in [(2,600,[0,-12,-12]),(3,6,[0,1,0]),(17,1,[0,0,0])]:
 d=mW+Cp[1]
 vF=[10*(c-d) for c in Cp];vDel=[2*(c-d) for c in Cp]
 # All fixed roots except zero have p-valuations >= -1; this
 # ensures usable near-infinity square unit ratios for the p2/3/17 rows.
 assert all(2*(d-c)>= (4 if p==2 else 1) for c in Cp)
 depths=[[6*d+i*c for i in (4,64,244)] for c in Cp]
 assert min(x for r in depths for x in r)>= (3 if p==2 else 1)
 vs=[2*d-12*c-2*int(p==2) for c in Cp];assert min(vs)>= {2:3,3:1,17:2}[p]
 rows.append(dict(p=p,W_depth=-mW,w_depth=-d,scale_depths=Cp,
      F_depth=vF,delta_depth=vDel,weights_depth=depths,
      two_tau_unit=True,pole_depths=vs))
print(json.dumps(dict(D=data['D'],h_small_valuations=[vp(h,p) for p in (2,3,17)],
    h_odd_labels_mod2=labels(2),p3_first_formal_return=P(4),
    p3_actual_labels=ls,p3_opp_U_V_QJ=opp,p3_inverse_chart_prod=G,p3_scale_mod9=C,
    p3_Pade_arg_mod3=[1,0],all_local_depths=rows),indent=2))
