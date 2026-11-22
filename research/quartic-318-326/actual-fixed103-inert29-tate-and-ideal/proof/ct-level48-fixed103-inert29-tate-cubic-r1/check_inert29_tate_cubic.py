#!/usr/bin/env python3
"""All 224 fixed level-48 flags; no moving CM multiplicities."""
from pathlib import Path
from hashlib import sha256
import json,sys
root=Path(__file__).resolve().parent.parent.parent
src=root/'high-hom-1120/heegner-compressed-trace/original-detectors-inert29-finite-receiver-r1/replay_inert29.py'
assert sha256(src.read_bytes()).hexdigest()=='e1f570297815f21b270374b01a5f0972ee0d1cb20f7123082de254e4318d08f5'
sys.path.insert(0,str(src.parent))
import replay_inert29 as m
S=m.roots_table()
C=sorted(Q for Q in m.curvepoints(S) if m.j48(*Q) in (0,2,25))
assert len(C)==224
E={m.phi(*Q) for Q in C};assert len(E)==112
H=(23,7);G=(14,m.f(0,13));T=(0,0)
assert m.pm(3,H) is None and m.pm(9,G) is None and m.pm(3,G) is not None
def f(A):
 assert A is not None
 x,y=A;return m.add(m.sub(y,m.mul(3,x)),4)
assert f(H)==0 and f(T)==4 and m.pw(4,280)==1
def direct(P):
 x,y=P;assert x
 v=m.div(m.add(m.add(m.mul(4,m.pw(x,2)),m.mul(9,x)),m.mul(3,y)),m.pw(x,2))
 assert v and v==f(m.p_add(P,T))
 return v
def t(P):
 v=f(m.p_add(P,T));assert v
 return m.pw(v,280)
gamma=t(G)
assert gamma==m.f(14,5) and m.pw(gamma,3)==1 and gamma!=1
D={m.pm(k,G):k for k in range(9)};assert len(D)==9
out=[];edges={}
for X,Y in C:
 A=m.phi(X,Y)
 P=m.pm(4,m.p_add(A,m.p_neg(m.p_fr(A))));k=D[P]%3
 h=direct(A);u=m.pw(h,560);assert u==m.pw(gamma,k)
 Z=m.mul(A[0],m.pw(X,2))
 t1=m.add(m.sub(X,2),m.div(m.mul(3,X),Z))
 t2=m.div(m.sub(m.sub(Z,m.mul(2,X)),1),X)
 assert (t1,t2) not in edges
 edges[t1,t2]=(X,Y,k)
 out.append([X,Y,t1,t2,h,k])
cyc=[(122,132),(741,132),(741,731),(558,731),(558,297),(122,297)]
cw=sum((-1)**i*edges[t][2] for i,t in enumerate(cyc))%3;assert cw==2
# Exact degree-four irreducibility control over F5.
p=[-9,0,-18,-8,3]
def at(x):return sum(c*x**i for i,c in enumerate(p))%5
assert all(at(x) for x in range(5))
def mul(a,b,u,v):
 return (a[0]*b[0]-v*a[1]*b[1])%5,(a[0]*b[1]+a[1]*b[0]-u*a[1]*b[1])%5
for u in range(5):
 for v in range(5):
  x=(1,0);a=b=0
  for c in p:
   a=(a+c*x[0])%5;b=(b+c*x[1])%5;x=mul(x,(0,1),u,v)
  assert a or b
don=Path(__file__).resolve().parent.parent/'ct-level48-fixed103-D1751-conductor241-pilot-r1'/'EXACT-FIXED103-CONDUCTOR241.json'
assert sha256(don.read_bytes()).hexdigest()=='b5291674384bbbfbcc094e2df042ae6fd654d020e38e6cd809caca474fd99efa'
z=json.loads(don.read_bytes())
t=sum(k*(r[0][k]-r[1][k]) for r in z['phase_histograms'] for k in range(9))
assert t==-86 and t%9==4 and m.pw(gamma,t%3)==gamma
print(json.dumps({'scope':'fixed cubic receiver and six-edge obstruction, no moving CM norm',
 'shift':list(T),'order3_tangent':list(H),'mu3_generator':m.coords((gamma,1))[0],
 'six_cycle':[[*i,*edges[i]] for i in cyc],'signed_cycle_residue':cw,'all_flags':out,
 'fixed_reference_exponent':t,'fixed_reference_cubic_result':m.coords((gamma,1))[0]},sort_keys=True,separators=(',',':')))
