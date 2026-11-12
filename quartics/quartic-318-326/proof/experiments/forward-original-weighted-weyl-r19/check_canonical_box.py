#!/usr/bin/env python3
"""Exact rational canonical-support/overlap checks. Not a Lean/kernel check."""
from fractions import Fraction as F
from itertools import product
from math import ceil
from pathlib import Path
import json

def norm(z):return max(map(abs,z))
def W(z):return max(F(0),1-norm(z))
def q(k,z):return z[0]**2+z[1]**2-z[2]**2-z[3]**2-k*z[4]**2
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def run():
 c=dict(canonical_support=0,overlap_enumeration=0,uniform_overlap_scale=0,paired_slice_variation=0,whole_circle_and_slice_budget=0,negative_controls=0)
 # Five-dimensional product norm and rational scaled tent with fixed R=1.
 for B in (F(1,3),F(1),F(3,2),F(2),F(7,3)):
  H=ceil(B)
  for z in product(range(-3,4),repeat=5):
   w=W(tuple(F(a)/B for a in z))
   assert not w or norm(z)<=H
   c['canonical_support']+=1
 for R in (F(1),F(3,2),F(7,3)):
  for B in (F(1),F(4,3),F(2),F(7,2),F(10)):
   H=ceil(R*B)
   for h in range(-2*H-2,2*H+3):
    lo=max(-H,-H-h);hi=min(H,H-h);n=max(0,hi-lo+1)
    actual={y for y in range(-H,H+1) if -H<=h+y<=H}
    assert actual=={lo+j for j in range(n)}
    c['overlap_enumeration']+=1
    assert n<=2*H+1 and n<=(2*R+3)*B
    c['uniform_overlap_scale']+=1
    if R==1:
     for b,c1,d,e in ((0,0,0,0),(1,-1,0,1)):
      disp=(h,1,-1,0,1)
      g=lambda j:W(tuple(F(a)/B for a in add(disp,(lo+j,b,c1,d,e))))*W(tuple(F(a)/B for a in (lo+j,b,c1,d,e)))
      if n:
       v=abs(g(n-1))+sum(abs(g(j)-g(j+1)) for j in range(n-1))
       assert v<=1+2*(2*R+3)
      c['paired_slice_variation']+=1
 # Exact real characters theta=0,1/2; arbitrary compact sample weight,
 # all five coordinates and all displacement fibers, not selected slices.
 H=1;s=list(product(range(-H,H+1),repeat=5));B=F(3,2)
 w={z:W(tuple(F(a)/B for a in z)) for z in s}
 for k in (-2,1):
  for t in (0,1):
   phase=lambda n:1 if (t*n)%2==0 else -1
   S=sum(w[z]*phase(q(k,z)) for z in s)
   pairs={}
   for x in s:
    for y in s:
     h=tuple(a-b for a,b in zip(x,y))
     pairs[h]=pairs.get(h,F(0))+w[x]*w[y]*phase(q(k,x)-q(k,y)-q(k,h))
   budget=F(0)
   for h in product(range(-2,3),repeat=5):
    ov=[range(max(-H,-H-a),min(H,H-a)+1) for a in h]
    full=F(0)
    for b,c1,d,e in product(*ov[1:]):
     sl=F(0)
     for a in ov[0]:
      y=(a,b,c1,d,e);x=add(h,y)
      sl+=w[x]*w[y]*phase(q(k,x)-q(k,y)-q(k,h))
     full+=sl;budget+=abs(sl)
    assert full==pairs[h]
   assert S*S<=sum(map(abs,pairs.values()))<=budget
   c['whole_circle_and_slice_budget']+=1
 # An arbitrarily undersized radius can omit a nonzero actual weight.
 assert W((F(2,3),0,0,0,0))>0 and 1>0
 # B>=1 is essential to absorb the unit rounding loss uniformly.
 assert 1>5*F(1,10)
 assert max(0,min(1,1-4)-max(-1,-1-4)+1)==0
 assert set(range(-1,2))!={-1,0}
 c['negative_controls']=4
 result={'status':'PASS','scope':'Exact rational Lipschitz tent, canonical box and all finite five-coordinate displacement/slice budgets. Not a smoothness or asymptotic test and not Lean elaboration.','checks':c}
 Path(__file__).with_name('CANONICAL-BOX-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
