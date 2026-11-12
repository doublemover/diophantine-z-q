#!/usr/bin/env python3
"""Exact complete integer-frequency and original five-coordinate displacement partitions; not Lean or minor decay."""
from fractions import Fraction as F
from math import gcd,floor
from itertools import product
from pathlib import Path
import json

def center(x):return x-floor(x+F(1,2))
def cap(N,x):return N if not x else min(N,F(1)/(2*abs(x)))
def cost(N,q,b):return N if b in (-1,0) else F(q,b) if b>0 else F(q,-b-1)
def run():
 count=dict(exact_frequency_partitions=0,endpoint_block_counts=0,complete_frequency_budgets=0,even_displacement_budgets=0,original_displacement_partition=0,negative_controls=0)
 for q in range(1,14):
  L=q//2+1;assert L>0 and 2*(L-1)<=q
  for lo,hi in [(-29,31),(-8,-1),(0,0),(5,3),(-L-1,L+1)]:
   for sparse in (False,True):
    s=[c for c in range(lo,hi+1) if not sparse or c%3]
    keys=set(c//L for c in s);fib={k:[c for c in s if c//L==k] for k in keys}
    assert sorted(c for k in keys for c in fib[k])==s
    assert all(k*L<=c<=k*L+L-1 for k in keys for c in fib[k])
    assert sum(c*c-3*c+1 for c in s)==sum(sum(c*c-3*c+1 for c in fib[k]) for k in keys)
    count['exact_frequency_partitions']+=1
    assert len(keys)<=max(0,hi//L-lo//L+1)
    if lo<=hi:
     assert max(0,hi//L-lo//L+1)<=F(hi-lo,L)+2<=F(2*(hi-lo),q)+2
    count['endpoint_block_counts']+=1
    for a in range(-2,3):
     if gcd(q,a)!=1:continue
     for e in (-1,0,1):
      t=F(a,q)+F(e,q*q)
      for N in (F(0),F(1),F(13)):
       budget=sum(cost(N,q,b) for b in range(-q,q+1))
       total=sum(cap(N,center(c*t)) for c in s)
       assert total<=len(keys)*budget
       count['complete_frequency_budgets']+=1
  for H in range(5):
   for a in range(-2,3):
    if gcd(q,a)!=1:continue
    for e in (-1,0,1):
     t=F(a,q)+F(e,q*q);N=F(2*H+1)
     budget=sum(cost(N,q,b) for b in range(-q,q+1))
     assert 4*H//L-((-4*H)//L)+1<=F(16*H,q)+2
     assert sum(cap(N,center(2*h*t)) for h in range(-2*H,2*H+1))<=(4*H//L-((-4*H)//L)+1)*budget
     count['even_displacement_budgets']+=1
 # Literal five-coordinate original-box ordered pairs and nonseparable weights.
 H=1;s=list(product(range(-H,H+1),repeat=5));weight=lambda z:1+sum((i+1)*v*v-(i+2)*v for i,v in enumerate(z))
 slices={}
 for x in s:
  for y in s:
   h=tuple(a-b for a,b in zip(x,y));bil=h[0]*y[0]+h[1]*y[1]-h[2]*y[2]-h[3]*y[3]-h[4]*y[4]
   key=(h,y[1:]);slices[key]=slices.get(key,0)+weight(x)*weight(y)*(-1 if bil%2 else 1)
 costs={}
 for (h,outer),v in slices.items():costs[h]=costs.get(h,0)+abs(v)
 assert set(costs)==set(product(range(-2,3),repeat=5))
 for q in (1,2,3,4,9,17):
  L=q//2+1;keys={2*h[0]//L for h in costs}
  assert sum(costs.values())==sum(sum(v for h,v in costs.items() if 2*h[0]//L==k) for k in keys)
  assert all(-4*H<=2*h[0]<=4*H for h in costs)
  assert all(k*L<=2*h[0]<=k*L+L-1 for k in keys for h in costs if 2*h[0]//L==k)
  assert len(keys)<=4*H//L-((-4*H)//L)+1
  count['original_displacement_partition']+=1
 # Negative frequencies require Euclidean floor, not truncation toward0.
 assert (-1)//3==-1 and int(F(-1,3))==0
 assert 4 not in range(-2,3) # dropping factor2 loses a legitimate H=1 frequency
 assert len({2*h[0] for h in costs})<len(costs) # frequency injection is NOT displacement injection
 assert set(range(-4,5))!={c for c in range(-4,5) if c//3 in (-1,0)} # edge blocks cannot be dropped
 count['negative_controls']=4
 result={'status':'PASS','scope':__doc__,'checks':count}
 Path(__file__).with_name('COMPLETE-BLOCK-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
