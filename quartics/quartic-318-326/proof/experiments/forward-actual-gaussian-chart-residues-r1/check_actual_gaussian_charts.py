#!/usr/bin/env python3
from itertools import product
import json,sympy as s
k,t,x,z,w=s.symbols('k t x z w')
P=k*w*w+2*t;PP=k*(t+2)*w*w-2*x*z
K=(k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2
D=(t*t+x*x)*(t*t+z*z);Ds=((t+2)**2+x*x)*((t+2)**2+z*z)
Q=k*(t+2)*w*w+2*t**3+8*t*t-2*t*x*z+8*t-2*x*z
assert s.expand(K-D-P*(P+2*t*t-2*x*z))==0
assert s.expand((t+2)**2*K-t*t*Ds-PP*Q)==0
assert s.expand(K.subs({t:-2,x:0})-k*k*w**4-4*z*z)==0
assert s.expand(K.subs({t:-2,z:0})-k*k*w**4-4*x*x)==0
c=dict(regular_residue_sets=0,exceptional_residue_sets=0,source_chart_comparisons=0,basis_permutations=0,actual_kappa_counterexamples=0)
for kap in [1,318,326]:
 a,b,cc,d,W,p=-5,-1,-5,-1,0,17;T=a+cc;X=b-d;Z=b+d
 assert a*a+b*b-cc*cc-d*d-kap*W*W==0
 assert ((a+1)**2+b*b)%p==((cc+1)**2+d*d)%p==0
 assert (kap*(T+2)*W*W-2*X*Z)%p==0
 assert ((T*T+X*X)*(T*T+Z*Z))%p==13
 assert kap%p and T%p;c['actual_kappa_counterexamples']+=1
for p in [2,3,5,7,11,13,17]:
 for kap in range(1,p):
  for T in range(1,p):
   zeros=[]
   for X,Z,W in product(range(p),repeat=3):
    pp=(kap*(T+2)*W*W-2*X*Z)%p
    kval=((kap*W*W-X*Z+T*T+2*T)**2+T*T*(X+Z)**2)%p
    if pp==kval==0:zeros.append((X,Z,W))
   if (T+2)%p:
    assert len(zeros)<=8*p
    for X,Z,W in zeros:assert (((T+2)**2+X*X)*((T+2)**2+Z*Z))%p==0
    c['regular_residue_sets']+=1
   else:
    assert len(zeros)<=4*p
    for X,Z,W in zeros:
     assert X*Z%p==0
     q=Z if X==0 else X
     assert (kap*kap*W**4+4*q*q)%p==0
    c['exceptional_residue_sets']+=1
# Original finite source, including both charts, checked before projecting or discarding parity.
for p in [3,5,7]:
 for kap in [1,318%p or 1,326%p or 1]:
  for a,b,cc,d,W in product(range(p),repeat=5):
   if (a*a+b*b-cc*cc-d*d-kap*W*W)%p:continue
   G=((a+1)**2+b*b)%p;H=((cc+1)**2+d*d)%p;X=(b-d)%p;Z=(b+d)%p
   for side in [False,True]:
    T=(a+cc if side else a-cc)%p
    if not T:continue
    f=(kap*(T+2)*W*W-2*X*Z if side else kap*W*W+2*T)%p
    kval=((kap*W*W-X*Z+T*T+2*T)**2+T*T*(X+Z)**2)%p
    assert (G==H==0)==(f==kval==0);c['source_chart_comparisons']+=1
# Same whole-basis residue permutation, not q(t+2). Upper triangular determinant q².
for p in [5,7,11]:
 for q in [2,3,6]:
  if q%p==0:continue
  for kap,T in [(1,1),(2,p-2),(3,2)]:
   if kap%p==0 or T%p==0:continue
   image={((q*a+b+cc)%p,(q*b+2*cc)%p,cc%p) for a,b,cc in product(range(p),repeat=3)}
   assert len(image)==p**3
   num=sum((kap*(T+2)*W*W-2*X*Z)%p==0 and ((kap*W*W-X*Z+T*T+2*T)**2+T*T*(X+Z)**2)%p==0 for X,Z,W in image)
   assert num<=8*p;c['basis_permutations']+=1
print(json.dumps({'status':'PASS','checks':c,'symbolic_identities':4,'local_lean':'NOT_RUN'},indent=2))
