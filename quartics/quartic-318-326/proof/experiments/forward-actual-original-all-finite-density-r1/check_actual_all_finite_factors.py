#!/usr/bin/env python3
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import json
C=Counter()
def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def sigma(k,p):
 if not prime(p):return F(1)
 if p==2:return F(8,7)
 if k%p==0:return F((p+1)**2,p*p+p+1)
 return (1-F(1,p**4))/(1-F(1,p**3))
def count(k,m,even=0,p=1):
 st={0:1}
 for c in [1,1,-1,-1,-k]:
  h=Counter(c*x*x%m for x in range(0,m,p if even else 1));t=Counter()
  for a,u in st.items():
   for b,v in h.items():t[(a+b)%m]+=u*v
  st=t
 return st[0]
for k,bad in [(318,{2:F(8,7),3:F(16,13),53:F(2916,2863)}),(326,{2:F(8,7),163:F(26896,26733)})]:
 G=E=S=T=P=F(1)
 for p in range(230):
  if prime(p):assert (k%p==0 or p==2)==(p in bad)
  g=sigma(k,p) if prime(p) and p not in bad else F(1)
  b=bad.get(p,F(1));s=sigma(k,p)
  assert s==g*b and s>0
  t=1-F(1,p**3) if prime(p) else F(1)
  assert t>0
  if prime(p):assert (s*t)>0
  G*=g;E*=b;S*=s;T*=t;P*=s*t
  assert S==G*E and P==S*T
  C['all_prime_factor_classifications']+=1
  C['actual_full_and_primitive_cutoff_products']+=1
 for p in [2,3,5,7]:
  Ns=[]
  for n in range(6 if p==2 else 4):
   m=p**n;N=count(k,m);Ns.append(N)
   if n>=2:
    primitive=N-count(k,m,1,p)
    assert primitive==N-p**5*Ns[n-2]
    assert F(primitive,p**(4*n))==F(N,p**(4*n))-F(Ns[n-2],p**(4*(n-2)))/p**3
    C['actual_all_prime_primitive_difference']+=1
print(json.dumps({'status':'PASS',**C},sort_keys=True))
