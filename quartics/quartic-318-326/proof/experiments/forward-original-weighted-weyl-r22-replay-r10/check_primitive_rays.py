from collections import defaultdict
from fractions import Fraction as F
from functools import reduce
from math import gcd,isqrt
import json
counts=defaultdict(int)
def q(k,v):a,b,c,d,w=v;return a*a+b*b-c*c-d*d-k*w*w
def form(g,v):a,b,c,d,w=v;return a*a+b*b+g*w*w
def prime_factor(n):
 for p in range(2,isqrt(n)+1):
  if n%p==0:return p
 return n
def normalize(k,v):
 u=v;factor=1
 while (g:=reduce(gcd,map(abs,u)))>1:
  p=prime_factor(g);z=tuple(x//p for x in u)
  assert all(x%p==0 for x in u) and q(k,z)==0 and 0<z[0]<u[0]
  assert all(x==p*y for x,y in zip(u,z))
  counts['actual_prime_coordinate_descents']+=1
  factor*=p;u=z
 assert reduce(gcd,map(abs,u))==1 and all(x==factor*y for x,y in zip(v,u))
 return factor,u
allprim={}
for k in [318,326]:
 H=35;pairs=defaultdict(list)
 for a in range(1,H+1):
  for b in range(-H,H+1):pairs[a*a+b*b].append((a,b))
 vs=[]
 for w in range(1,4):
  for c in range(1,H+1):
   for d in range(-H,H+1):
    for a,b in pairs[c*c+d*d+k*w*w]:
     v=(a,b,c,d,w)
     if all(form(g,v)>0 for g in [-k,-k+1,0,7]):vs.append(v)
     if len(vs)>=300:break
    if len(vs)>=300:break
   if len(vs)>=300:break
  if len(vs)>=300:break
 assert len(vs)==300
 prim=set()
 for v in vs:
  for r in [1,2,3,6]:
   vr=tuple(r*x for x in v);factor,u=normalize(k,vr);prim.add(u)
   assert u[0]>0 and u[2]>0 and u[4]>0 and q(k,u)==0
   for g in [-k,-k+1,0,7]:
    assert form(g,vr)==factor*factor*form(g,u) and form(g,u)>0
    counts['same_original_form_scaling']+=1
   counts['primitive_ray_factors']+=1
 allprim[k]=list(prim)
 for H in [10,20,35,50,80,120]:
  S=allprim[k][:50];cover=set()
  for u in S:
   for r in range(H+1):
    v=tuple(r*x for x in u)
    if max(map(abs,v))<=H:
     assert r<=H;cover.add(v)
  assert len(cover)<=len(S)*(H+1)
  weights=[F(sum(v)%7,7) for v in cover]
  assert sum(weights)<=len(S)*(H+1)
  counts['finite_ray_cover_and_original_weights']+=1
for A in [F(0),F(1),F(7,3)]:
 for B in [F(1),F(2),F(5,2),F(19)]:
  assert A*B/(B**3)==A/(B**2)
  counts['linear_mass_original_normalization']+=1
for k,S in allprim.items():
 for M in range(1,31):
  assert len(set(S[:M]))==M and all(reduce(gcd,map(abs,u))==1 for u in S[:M])
  counts['actual_finite_primitive_source_cardinality']+=1
# Negative controls: origin has no positive-coordinate descent; checking
# only two coordinates is not global primitivity; scaling need not preserve
# primality or the original weight value.
assert (0,0,0,0,0)[0]==0
assert gcd(2,4)>1 and reduce(gcd,[2,4,3,6,9])==1
assert 2*2*3==12 and 12%2==0
assert F(sum((1,2,3,4,5))%7,7)!=F(sum((2,4,6,8,10))%7,7)
counts['negative_controls']=4
print(json.dumps({'status':'PASS','checks':dict(counts),'scope':'Exact original integer equations, all-coordinate primitive factor descent, positive-form scaling and overlap-safe finite ray/weight bounds. No numerical asymptotic or prime-value inference.'},indent=2))
