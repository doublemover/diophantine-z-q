#!/usr/bin/env python3
"""Exact rational Lipschitz models and original finite slice identities, not Lean."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def add(x,y):return tuple(a+b for a,b in zip(x,y))
def line(y,v,j):return tuple(a+j*b for a,b in zip(y,v))
def norm(x):return max(map(abs,x))
def W(x):return max(F(0),1-norm(x))
def Q(k,x):return x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2
def bil(k,h,y):return h[0]*y[0]+h[1]*y[1]-h[2]*y[2]-h[3]*y[3]-k*h[4]*y[4]
def weight(x):return 1+sum((i+1)*z*z-(i+2)*z for i,z in enumerate(x))
def phase_sum(q,terms):
 p=[0]*q
 for phase,w in terms:p[phase%q]+=w
 return p

def run():
 counts=dict(scaled_increments=0,uniform_paired_variation=0,interval_overlaps=0,box_base_points=0,exact_slice_aggregation=0,interval_phase_identity=0,negative_controls=0)
 cases=[((0,0,0,0,0),(1,0,0,0,0),(2,-1,0,0,0)),
        ((-4,1,0,-1,0),(1,-1,2,0,1),(-1,0,1,2,0)),
        ((1,1,1,1,1),(0,0,0,0,0),(0,0,0,0,0))]
 for B in (F(1,2),F(1),F(3),F(7,2),F(10)):
  for N in (0,1,2,5,10):
   R=F(N)/B
   for y,v,h in cases:
    u=lambda j:W(tuple(F(z)/B for z in add(h,line(y,v,j))))
    vv=lambda j:W(tuple(F(z)/B for z in line(y,v,j)))
    for j in range(N):
     assert abs(u(j)-u(j+1))<=norm(v)/B
     assert abs(vv(j)-vv(j+1))<=norm(v)/B
     counts['scaled_increments']+=2
    g=lambda j:u(j)*vv(j)
    variation=abs(g(N))+sum(abs(g(j)-g(j+1)) for j in range(N))
    assert variation<=1+2*R*norm(v)
    counts['uniform_paired_variation']+=1
 for lo in range(-3,4):
  for hi in range(-4,5):
   for h in range(-5,6):
    s=set(range(lo,hi+1));overlap={y for y in s if h+y in s}
    a=max(lo,lo-h);b=min(hi,hi-h)
    assert overlap==set(range(a,b+1))=={a+j for j in range(max(0,b-a+1))}
    counts['interval_overlaps']+=1
 boxes=[((-1,0),(-1,1),(0,1),(-1,0),(0,2)),((),(0,),(0,),(0,),(0,))]
 for sets in boxes:
  s=set(product(*sets))
  for h in [(0,)*5,(1,0,0,0,0),(-1,0,1,0,2),(4,)*5]:
   overlaps=[tuple(y for y in sj if hj+y in sj) for sj,hj in zip(sets,h)]
   actual={y for y in s if add(h,y) in s};constructed=set(product(*overlaps))
   assert actual==constructed;counts['box_base_points']+=1
   for q in (1,2,3,5,8):
    for k in (-3,0,2):
     paired=phase_sum(q,((2*bil(k,h,y),weight(x)*weight(y)) for x in s for y in s if tuple(a-b for a,b in zip(x,y))==h))
     sliced=phase_sum(q,((2*bil(k,h,(a,b,c,d,e)),weight(add(h,(a,b,c,d,e)))*weight((a,b,c,d,e)))
       for b,c,d,e in product(*overlaps[1:]) for a in overlaps[0]))
     assert paired==sliced;counts['exact_slice_aggregation']+=1
 for q in (1,2,3,5,8):
  for k in (-3,0,2):
   for lo,hi in [(-3,2),(0,-1),(2,2)]:
    h=(1,0,2,-1,1);base=(lo,1,-1,0,2);v=(1,0,0,0,0)
    actual=phase_sum(q,((Q(k,add(h,line(base,v,j)))-Q(k,line(base,v,j)),weight(add(h,line(base,v,j)))*weight(line(base,v,j))) for j in range(max(0,hi-lo+1))))
    expected=phase_sum(q,((Q(k,h)+2*bil(k,h,(a,1,-1,0,2)),weight(add(h,(a,1,-1,0,2)))*weight((a,1,-1,0,2))) for a in range(lo,hi+1)))
    assert actual==expected;counts['interval_phase_identity']+=1
 assert {y for y in range(3) if y+1 in range(3)} != set(range(3))
 assert set(range(-2,3)) != set(range(-2,2))
 assert abs(F(0)-F(1))>F(1,2) # inverse-scale factor cannot be arbitrarily halved
 counts['negative_controls']=3
 result={'status':'PASS','scope':'Exact rational Lipschitz tent models and finite original integer/group-ring slice identities. Tent model is not smooth. Does not verify Lean, smooth mean-value analysis, minor integral estimates or asymptotic decay.','checks':counts}
 Path(__file__).with_name('UNIFORM-SLICE-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
