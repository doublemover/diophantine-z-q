#!/usr/bin/env python3
from itertools import product
from collections import Counter
import json
C=Counter()
def Q(k,x):a,b,c,d,w=x;return a*a+b*b-c*c-d*d-k*w*w
def count(k,m,regular=False):
 def run(first_even):
  st={0:1}
  for i,c in enumerate([1,1,-1,-1,-k]):
   vals=range(0,m,2) if first_even and i<4 else range(m)
   h=Counter(c*x*x%m for x in vals);t=Counter()
   for a,u in st.items():
    for b,v in h.items():t[(a+b)%m]+=u*v
   st=t
  return st[0]
 return run(False)-run(True) if regular else run(False)
for k in [0,1,2,6,318,326,-1]:
 for e in range(4):
  m=2**(e+3);d=m//2
  bases=[]
  for x in product(range(m),repeat=5):
   if Q(k,x)%m==0 and any(t%2 for t in x[:4]):bases.append(x)
   if e>0 and len(bases)>=300:break
  success=0
  for x in bases:
   i=next(i for i in range(4) if x[i]%2)
   y=list(x);y[i]=(y[i]+d)%m;y=tuple(y)
   assert Q(k,y)%m==0
   assert tuple(t%2 for t in y)==tuple(t%2 for t in x)
   assert next(j for j in range(4) if y[j]%2)==i
   z=list(y);z[i]=(z[i]+d)%m;assert tuple(z)==x
   assert (Q(k,y)%(2*m)==0)!=(Q(k,x)%(2*m)==0)
   integer=list(x);integer[i]+=d
   assert (Q(k,integer)-Q(k,x)-m)%(2*m)==0
   assert (Q(k,integer)-Q(k,y))%(2*m)==0
   success+=Q(k,x)%(2*m)==0
   C['actual_original_pivot_involutions']+=1
   C['next_bit_switches_and_carries']+=1
  if e==0:
   assert len(bases)==count(k,m,True)
   assert len(bases)==2*success
   C['actual_whole_successful_half_counts']+=1
  assert count(k,2*m,True)==16*count(k,m,True)
  C['independent_whole_regular_recurrences']+=1
  for x in bases[:24]:
   valid=0
   for h in product(range(2),repeat=5):
    y=tuple(a+m*b for a,b in zip(x,h))
    assert (Q(k,y)%(2*m)==0)==(Q(k,x)%(2*m)==0)
    valid+=Q(k,y)%(2*m)==0
    C['actual_32_or_zero_digit_tests']+=1
   assert valid==(32 if Q(k,x)%(2*m)==0 else 0)
   C['actual_ambient_fibers']+=1
print(json.dumps({'status':'PASS',**C},sort_keys=True))
