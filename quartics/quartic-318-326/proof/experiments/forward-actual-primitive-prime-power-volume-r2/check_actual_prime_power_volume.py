#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from collections import Counter
import json
C=Counter()
def Q(k,x):a,b,c,d,w=x;return a*a+b*b-c*c-d*d-k*w*w
def count(k,m,allowed):
 state={0:1}
 for c in [1,1,-1,-1,-k]:
  h=Counter(c*x*x%m for x in allowed)
  nxt=Counter()
  for a,u in state.items():
   for b,v in h.items():nxt[(a+b)%m]+=u*v
  state=nxt
 return state[0]
for p in [3,5,7]:
 for k in [1,2,318,326,-1]:
  if k%p==0:continue
  for e in range(4 if p==3 else 3):
   m=p**(e+1)
   actual=count(k,m,range(m))-count(k,m,range(0,m,p))
   assert actual==(p**4-1)*(p**4)**e
   assert F(actual,m**4)==1-F(1,p**4)>0
   C['independent_whole_primitive_counts']+=1
   C['exact_primitive_volumes']+=1
# Actual full preimage sets at successive levels, not symbolic cardinal recurrence.
for p in [3,5]:
 for k in [1,2,318,326,-1]:
  if k%p==0:continue
  bases=[x for x in product(range(p),repeat=5) if Q(k,x)%p==0 and any(x)]
  for R in [[],bases[:1],bases[:2],bases[-2:]]:
   S=set(R);m=p
   for e in range(3 if p==3 else 2):
    assert len(S)==len(R)*p**(4*e)
    assert F(len(S),m**4)==F(len(R),p**4)
    assert F(len(S),(p**4-1)*p**(4*e))==F(len(R),p**4-1)
    assert all(Q(k,x)%m==0 and any(t%p for t in x) for x in S)
    C['actual_subset_tower_levels']+=1
    C['actual_event_ratio']+=1
    if e==(2 if p==3 else 1):break
    T=set()
    for x in S:
     for h in product(range(p),repeat=5):
      y=tuple(xx+m*hh for xx,hh in zip(x,h))
      if Q(k,y)%(m*p)==0:
       assert tuple(t%m for t in y)==x
       T.add(y)
       C['actual_ambient_lifts']+=1
    assert len(T)==len(S)*p**4
    S=T;m*=p
print(json.dumps({'status':'PASS',**C},sort_keys=True))
