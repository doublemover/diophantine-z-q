#!/usr/bin/env python3
"""Exact centered-frequency packing and resonance-aware reciprocal sums; not Lean or global minor decay."""
from fractions import Fraction as F
from math import gcd,floor
from pathlib import Path
import json

def center(x):return x-floor(x+F(1,2))
def cap(N,x):return N if not x else min(N,F(1)/(2*abs(x)))
def cost(N,q,b):return N if b in (-1,0) else F(q,b) if b>0 else F(q,-b-1)
def run():
 c=dict(full_short_block_injections=0,pointwise_bins=0,complete_reciprocal_sums=0,harmonic_bin_identity=0,resonant_terms_retained=0,negative_controls=0)
 for q in range(1,13):
  for a in range(-q,q+1):
   if gcd(q,a)!=1:continue
   for e in (F(-1),F(-1,2),F(0),F(1,2),F(1)):
    t=F(a,q)+e/(q*q)
    for lo in (-q,0,q):
     points=[center(j*t) for j in range(lo,lo+q//2+1)]
     bins=[floor(2*q*x) for x in points]
     assert len(bins)==len(set(bins)) and all(-q<=b<=q for b in bins)
     c['full_short_block_injections']+=1
     for N in map(F,(0,1,10,q*q)):
      for x,b in zip(points,bins):
       assert cap(N,x)<=cost(N,q,b)
       c['pointwise_bins']+=1
       if not x:
        assert cap(N,x)==N
        c['resonant_terms_retained']+=1
      total=sum(cap(N,x) for x in points)
      budget=sum(cost(N,q,b) for b in range(-q,q+1))
      assert total<=budget
      c['complete_reciprocal_sums']+=1
      hq=sum(F(1,j) for j in range(1,q+1));hprev=sum(F(1,j) for j in range(1,q))
      assert budget==2*N+q*(hq+hprev)<=2*N+2*q*hq
      c['harmonic_bin_identity']+=1
 assert cap(F(10),F(0))==10 # a totalized zero reciprocal would erase resonance
 assert center(F(0))==center(F(2)*F(1,2)) # too-long interval is not injective
 assert floor(20*F(-1,40))==-1 and floor(20*F(1,40))==0
 assert cap(F(10),F(-1,40))+cap(F(10),F(1,40))>10 # both central bins needed
 x=F(-51,1000);b=floor(20*x)
 assert b==-2 and cap(F(100),x)>F(10,-b) # negative endpoint uses -b-1
 c['negative_controls']=4
 result={'status':'PASS','scope':__doc__,'checks':c}
 Path(__file__).with_name('RECIPROCAL-BIN-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
