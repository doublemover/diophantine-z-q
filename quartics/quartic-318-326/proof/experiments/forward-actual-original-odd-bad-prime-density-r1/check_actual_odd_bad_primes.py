#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as F
from collections import Counter
import json
C=Counter()
def Q(k,x):a,b,c,d,w=x;return a*a+b*b-c*c-d*d-k*w*w
def count(k,m,vals=None):
 if vals is None:vals=range(m)
 st={0:1}
 for c in [1,1,-1,-1,-k]:
  h=Counter(c*x*x%m for x in vals);t=Counter()
  for a,u in st.items():
   for b,v in h.items():t[(a+b)%m]+=u*v
  st=t
 return st[0]
for p,k in [(3,3),(3,6),(3,318),(5,5),(5,10),(7,7),(7,21)]:
 assert k%p==0 and k%(p*p)!=0
 for a,b,c,d in product(range(p),repeat=4):
  for w in range(p*p):
   x=(p*a,p*b,p*c,p*d,w)
   if Q(k,x)%(p*p)==0:assert w%p==0
   C['valuation_one_obstructions']+=1
 bases=[x for x in product(range(p),repeat=5) if Q(k,x)%p==0 and any(x[:4])]
 assert len(bases)==p**4+p**3-p**2-p
 C['actual_regular_base_counts']+=1
 for x in bases[:5]+bases[-5:]:
  grad=(2*x[0],2*x[1],-2*x[2],-2*x[3],-2*k*x[4])
  assert any(g%p for g in grad)
  n=0
  for h in product(range(p),repeat=5):
   y=tuple(xx+p*hh for xx,hh in zip(x,h))
   if Q(k,y)%(p*p)==0:n+=1;assert any(t%p for t in y[:4])
   C['bad_prime_actual_digit_tests']+=1
  assert n==p**4
  C['bad_prime_actual_p4_fibers']+=1
 if p<=5:
  Ns=[]
  for n in range(5 if p==3 else 4):
   m=p**n;N=count(k,m);Ns.append(N)
   sigma=F((p+1)**2,p*p+p+1);r=F(1,p**3)
   v1=1+F(1,p)-F(1,p*p)
   V=sigma+((1 if n%2==0 else v1)-sigma)*r**(n//2)
   assert F(N,p**(4*n))==V
   if n>=2:
    primitive=N-count(k,m,range(0,m,p))
    assert primitive==(p**4+p**3-p*p-p)*p**(4*(n-1))
    assert N==(p**4+p**3-p*p-p)*p**(4*(n-1))+p**5*Ns[n-2]
    C['actual_bad_primitive_and_full_recurrences']+=1
   C['independent_bad_full_count_formulas']+=1
for k,p,s in [(318,3,F(16,13)),(318,53,F(2916,2863)),(326,163,F(26896,26733))]:
 assert k%p==0 and k%(p*p)!=0
 assert s==F((p+1)**2,p*p+p+1)
 assert count(k,p)==p**4+p**3-p*p
 assert count(k,p)-p==p**4+p**3-p*p-p
 C['original_quartic_odd_bad_places']+=1
print(json.dumps({'status':'PASS',**C},sort_keys=True))
