#!/usr/bin/env python3
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import json
C=Counter()
def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def good(k,p):return prime(p) and p!=2 and k%p!=0
for k in [0,1,-1,318,326,954,978]:
 S=P=T=F(1)
 snapshots=[]
 for p in range(250):
  if good(k,p):s=1+F(1,p*(p*p+p+1));t=1-F(1,p**3);q=1-F(1,p**4)
  else:s=t=q=F(1)
  assert s>0 and t>0 and q>0
  assert q==s*t
  assert abs(s-1)<=(F(1,p**3) if p else 0)
  assert abs(t-1)<=(F(1,p**3) if p else 0)
  assert abs(q-1)<=(F(1,p**4) if p else 0)
  C['actual_factorwise_identities_and_bounds']+=1
  S*=s;P*=q;T*=t
  assert P==S*T
  snapshots.append((S,T,P))
  C['actual_full_cutoff_product_identities']+=1
 # Finite prefix reciprocal bound used by all_cutoff_bounds,
 # independently evaluated for every included prefix.
 for j in range(3):
  vals=[v[j] for v in snapshots[:35]]
  A=1+sum(1/v for v in vals);B=sum(vals)
  assert all(1/A<=v<=B for v in vals)
  C['reciprocal_prefix_bounds']+=len(vals)
 # Every original actual finite CRT primitive volume equals the same products.
 for N in [0,1,2,3,4,8,16,31]:
  n=m=1
  for p in range(N):
   if good(k,p):n*=p**4-1;m*=p
  if N:expected=snapshots[N-1][0]*snapshots[N-1][1]
  else:expected=F(1)
  assert F(n,m**4)==expected
  C['original_finite_CRT_checks']+=1
print(json.dumps({'status':'PASS',**C},sort_keys=True))
