#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod, floor, isqrt
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import hermite_normal_form
checks={'whole_bases':0,'same_point_inverse':0,'common_cutoffs':0,'original_point_tails':0,'good_family_unions':0,'overlap_families':0}
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def mem(ps,k,ss,v):
 x,z,w=v
 return all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ss))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,v):return tuple(a*x for x in v)
for ps in [(),(3,),(5,),(3,5)]:
 M=prod(ps)
 for k in [1,2]:
  for ss in product(*([None]+list(range(p)) for p in ps)):
   vs=sorted([v for v in product(range(-M,M+1),repeat=3) if v!=(0,0,0) and mem(ps,k,ss,v)],key=lambda v:dot(v,v))
   u=vs[0];v=next(v for v in vs if cross(u,v)!=(0,0,0));n=cross(u,v)
   w=next(w for w in vs if dot(n,w)!=0)
   residues=[v for v in product(range(M),repeat=3) if mem(ps,k,ss,v)]
   generators=residues+[(M,0,0),(0,M,0),(0,0,M)]
   H=hermite_normal_form(S.Matrix.hstack(*(S.Matrix(v) for v in generators)))
   assert abs(H.det())==M*M
   G=0;z=(0,0,0)
   for j in range(3):
    h=tuple(map(int,H[:,j]));value=dot(n,h)
    if not value:continue
    a,b,g=map(int,S.gcdex(G,value))
    z=add(scale(a,z),scale(b,h));G=g
   assert G>0 and dot(n,z)==G
   D=dot(n,n);uu=dot(u,u);vv=dot(v,v);uv=dot(u,v)
   A=Q(dot(u,z)*vv-dot(v,z)*uv,D);B=Q(dot(v,z)*uu-dot(u,z)*uv,D)
   za=add(add(z,scale(-floor(A+Q(1,2)),u)),scale(-floor(B+Q(1,2)),v))
   assert dot(n,za)==G and mem(ps,k,ss,za)
   C=S.Matrix.hstack(S.Matrix(u),S.Matrix(v),S.Matrix(za));Ci=C.inv()
   assert abs(C.det())==M*M
   assert dot(za,za)<=4*dot(w,w)
   assert uu<=vv<=dot(w,w) and 2*abs(uv)<=uu
   checks['whole_bases']+=1
   TT=isqrt(dot(w,w))
   if TT*TT<dot(w,w):TT+=1
   for T in [TT,TT+1]:
    for R in [2,4,6]:
     A=isqrt(64*R*R//dot(u,u));Bb=isqrt(64*R*R//dot(v,v));Cc=isqrt(16*R*R//dot(w,w))
     cutoff=4*R//T
     assert cutoff<=min(A,Bb,Cc)
     checks['common_cutoffs']+=1
     points=[y for y in product(range(-R,R+1),repeat=3) if dot(y,y)<=R*R and mem(ps,k,ss,y)]
     for y in points:
      cs=tuple(map(int,Ci*S.Matrix(y)))
      assert tuple(C*S.Matrix(cs))==y
      assert all(abs(c)<=b for c,b in zip(cs,[A,Bb,Cc]))
      checks['same_point_inverse']+=1
     for Y in [1,2]:
      primes=[int(p) for p in S.primerange(Y+1,cutoff+1) if k%p and M%p]
      for side in [False,True]:
       def obs(y,p):
        x,z,w=y
        P=k*(M+2)*w*w-2*x*z if side else k*w*w+2*M
        D=(M*M+x*x)*(M*M+z*z)
        return P%p==0 and D%p==0
       obstructed=[y for y in points if any(obs(y,p) for p in primes)]
       assert len(obstructed)*M*M*Y<=110592*R**3
       checks['original_point_tails']+=1
# Aggregate overlapping actual good lattice families directly.
for p in [3,5]:
 for T in [2,4,6]:
  R=4;Y=1;sets=[]
  for s in [None]+list(range(p)):
   small=[y for y in product(range(-T,T+1),repeat=3) if dot(y,y)<=T*T and mem([p],1,[s],y)]
   if S.Matrix.hstack(*(S.Matrix(y) for y in small)).rank()<3:continue
   primes=[q for q in S.primerange(Y+1,4*R//T+1) if p%q]
   ss=set()
   for y in product(range(-R,R+1),repeat=3):
    if dot(y,y)>R*R or not mem([p],1,[s],y):continue
    x,z,w=y
    if any((w*w+2*p)%q==0 and ((p*p+x*x)*(p*p+z*z))%q==0 for q in primes):ss.add(y)
   sets.append(ss)
  union=set().union(*sets)
  assert len(union)<=sum(map(len,sets))
  assert len(union)*p*p*Y<=len(sets)*110592*R**3
  checks['good_family_unions']+=1
  if len(union)<sum(map(len,sets)):checks['overlap_families']+=1
for name in ['OriginalSieveFrame318','OriginalNormPointSieveTail318','OriginalCommonGoodCutoff318','OriginalGoodLatticeSieveUnion318']:
 text=(Path(__file__).parent/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks)
