#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod,gcd
from pathlib import Path
root=Path(__file__).resolve().parent
checks={'family_radius_counts':0,'actual_short_numerators':0,'floor_coordinate_cases':0}
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def length(v):return dot(v,v)
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
for ps in [[],[3],[5],[3,5]]:
 M=prod(ps);vs=list(product(range(-M,M+1),repeat=3))
 for k in [1,2]:
  data=[]
  for ts in product(*([None]+list(range(p)) for p in ps)):
   q=prod(p for p,s in zip(ps,ts) if s is not None);r=M//q
   A=next(a for a in range(q) if all((a-k*s*s)%p==0 for p,s in zip(ps,ts) if s is not None))
   D=next(d for d in range(M) if all((d-(0 if s is None else s))%p==0 for p,s in zip(ps,ts)))
   basis=[(r,A*r,D*r),(0,q,0),(0,0,M)]
   def mem(v):
    x,z,w=v
    return all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ts))
   L=sorted([v for v in vs if v!=(0,0,0) and mem(v)],key=length)
   u=L[0];v=next(v for v in L if cross(u,v)!=(0,0,0));n=cross(u,v)
   w=next(w for w in L if dot(n,w)!=0);G=gcd(*(dot(n,b) for b in basis))
   num=tuple(Q(M*x,G) for x in n)
   assert all(x.denominator==1 for x in num) and num!=(0,0,0)
   assert all(dot(num,b)%M==0 for b in basis)
   data.append((length(w),num));checks['actual_short_numerators']+=1
  for T in [Q(i,2) for i in range(1,41)]:
   R=Q(2*M,1)/T;B=R.numerator//R.denominator
   bad=[num for ell,num in data if ell>T*T]
   for num in bad:
    assert length(num)<R*R
    assert all(abs(x)<=B for x in num)
    checks['floor_coordinate_cases']+=1
   assert len(bad)<=27*4**len(ps)*B**3
   assert len(bad)*T**3<=216*4**len(ps)*M**3
   checks['family_radius_counts']+=1
# Critical negative control: floor applies to INTEGER COORDINATES, not norm.
v=(1,1,0);A=Q(3,2);B=1
assert length(v)<A*A and all(abs(x)<=B for x in v) and length(v)>B*B
# Exact real constant conversion, including empty B=0.
for M in range(1,20):
 for T in [Q(i,3) for i in range(1,100)]:
  A=Q(2*M,1)/T;B=A.numerator//A.denominator
  assert B*T<=2*M and 27*B**3*T**3<=216*M**3
text=(root/'OriginalThirdMinimumTail318.lean').read_text()
for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'1881 exact floor constant conversions; cube-vs-ball negative control')
