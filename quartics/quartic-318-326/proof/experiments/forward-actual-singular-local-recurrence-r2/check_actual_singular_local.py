#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as F
from collections import Counter
import json
C=Counter()
def Q(k,x):a,b,c,d,w=x;return a*a+b*b-c*c-d*d-k*w*w
def count(k,m,vals):
 a={0:1}
 for c in [1,1,-1,-1,-k]:
  h=Counter(c*x*x%m for x in vals);b=Counter()
  for x,u in a.items():
   for y,v in h.items():b[(x+y)%m]+=u*v
  a=b
 return a[0]
for p,m in [(2,1),(3,1),(3,2),(3,3),(5,1)]:
 for k in [1,2,318,326,-1]:
  n=p*p*m
  orig=set();lower=set();fibers=Counter()
  for z in product(range(m*p),repeat=5):
   y=tuple(p*t for t in z)
   assert all(0<=t<n and t%p==0 for t in y)
   assert tuple(t//p for t in y)==z
   assert (Q(k,y)%n==0)==(Q(k,z)%m==0)
   C['actual_scaling_equivalences']+=1
   if Q(k,z)%m==0:
    orig.add(y);lower.add(z);fibers[tuple(t%m for t in z)]+=1
  bases={x for x in product(range(m),repeat=5) if Q(k,x)%m==0}
  assert set(fibers)==bases and all(v==p**5 for v in fibers.values())
  assert len(orig)==len(lower)==len(bases)*p**5
  C['actual_singular_bijections']+=1
  C['all_free_last_digit_fibers']+=len(bases)
for p in [3,5,7]:
 for k in [1,2,318,326,-1]:
  if k%p==0:continue
  counts=[]
  for e in range(5 if p==3 else 4):
   n=p**e;N=count(k,n,range(n));counts.append(N)
   C['whole_modulus_counts']+=1
   if e==0:assert N==1
   elif e==1:assert N==p**4
   else:
    singular=count(k,n,range(0,n,p))
    assert singular==p**5*counts[e-2]
    primitive=N-singular
    assert primitive==(p**4-1)*p**(4*(e-1))
    assert N==(p**4-1)*p**(4*(e-1))+p**5*counts[e-2]
    assert F(N,p**(4*e))==1-F(1,p**4)+F(counts[e-2],p**(4*(e-2)))/p**3
    C['whole_actual_recurrences']+=1
    C['normalized_actual_recurrences']+=1
print(json.dumps({'status':'PASS',**C},sort_keys=True))
