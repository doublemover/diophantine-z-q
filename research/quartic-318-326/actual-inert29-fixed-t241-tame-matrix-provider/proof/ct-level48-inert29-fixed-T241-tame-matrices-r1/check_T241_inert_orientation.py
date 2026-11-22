#!/usr/bin/env python3
"""Check the fixed arcs on one inert trace-zero W frame, not a moving CM orbit."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,sys
base=Path(__file__).resolve().parent
src=base.parent.parent/'high-hom-1120/heegner-compressed-trace/original-detectors-inert29-finite-receiver-r1/replay_inert29.py'
assert sha256(src.read_bytes()).hexdigest()=='e1f570297815f21b270374b01a5f0972ee0d1cb20f7123082de254e4318d08f5'
sys.path.insert(0,str(src.parent))
import replay_inert29 as m
J=241;D=-17*103*17%J
assert D==117 and pow(D,120,J)==240
assert pow(17,120,J)==pow(103,120,J)==240  # (q/241)=(17/241)=-1
A=json.loads((base/'EXACT-INERT29-FIXED-T241-MATRICES.json').read_text())
def mv(a,b,v,n):return tuple((a[i]*v[0]+b[i]*v[1])%n for i in [0,1])
def norm(v,n):
 a,b=v;p=2 if n==16 else 3
 return (1,b*pow(a,-1,n)%n) if a%p else (a*pow(b,-1,n)%n,1)
def code(z):return m.f(*z)
G=(14,m.f(0,13));code9={m.pm(i,G):i for i in range(9)}
def phase(q):
 P=m.phi(*q);return code9[m.pm(4,m.p_add(P,m.p_neg(m.p_fr(P))))]
tab={int(j):{(tuple(a),tuple(b)):((code(X),code(Y)),phase((code(X),code(Y)))) for a,b,X,Y in L} for j,L in A['flags'].items()}
L=[(1,k) for k in range(J)]+[(0,1)]
def chi(q):return (1 if q==1 else -1) if q else 0
C=[chi(pow((a*a-D*b*b)%J,120,J)) for a,b in L]
assert 0 not in C and C.count(1)==C.count(-1)==121
S={};W={}
for j0,L in sorted(A['arcs'].items(),key=lambda z:int(z[0])):
 j=int(j0);H=[0]*9
 for (a,b),(Q,P0) in tab[j].items():
  v=0
  for sign,(k,u1,u2,v1,v2) in zip(C,L):
   x=norm(mv(u1,u2,a,16),16);y=norm(mv(v1,v2,b,3),3)
   v+=sign*tab[k][x,y][1]
  H[v%9]+=1
  if v%3 and j not in W:W[j]=[a,b,Q,v%9]
 S[j]=H
assert len(W)==3  # local orientation not uniformly killed at any of the 3 models
print(json.dumps(dict(scope='finite trace-zero inert orientation control, no moving CM index',
 D_mod241=D,inert_line_sign_counts=[121,121],frame_histograms=S,maximal_order_witnesses=W),
 sort_keys=True,separators=(',',':')))
