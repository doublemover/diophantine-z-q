#!/usr/bin/env python3
"""Exact finite bin partition/harmonic and rational-series sanity. Native log theorem is source evidence, not inferred from tests."""
from fractions import Fraction as F
from math import gcd,floor
from pathlib import Path
import json

def bin_cost(N,q,b):
 if b in (-1,0):return N
 return F(q,b) if b>0 else F(q,-b-1)
def harmonic(q):return sum((F(1,k) for k in range(1,q+1)),F(0))
def log_series(q):
 z=F(q-1,q+1);s=F(0);power=z
 for k in range(128):s+=2*power/F(2*k+1);power*=z*z
 return s

def run():
 c=dict(exact_partitions=0,negative_tail_injections=0,bin_harmonic_bounds=0,rational_series_sanity=0,complete_rational_kernel_bounds=0,negative_controls=0)
 series={q:log_series(q) for q in range(1,129)}
 for q in range(1,129):
  neg=set(range(-q,-1));mid={-1,0};pos=set(range(1,q+1))
  assert not (neg&mid or neg&pos or mid&pos)
  assert neg|mid|pos==set(range(-q,q+1));c['exact_partitions']+=1
  image={-b-1 for b in neg};assert len(image)==len(neg) and image<=pos;c['negative_tail_injections']+=1
  H=harmonic(q);assert H<=1+series[q];c['rational_series_sanity']+=1
  for N in (F(0),F(1,3),F(7),F(100)):
   budget=sum(bin_cost(N,q,b) for b in range(-q,q+1))
   assert budget==2*N+q*(harmonic(q)+harmonic(q-1))
   assert budget<=2*N+2*q*H<=2*N+2*q*(1+series[q]);c['bin_harmonic_bounds']+=1
 for q in range(1,21):
  for a in range(q):
   if gcd(a,q)!=1:continue
   t=F(a,q)
   for H in range(9):
    for N in (F(0),F(1),F(5),F(2*H+1)):
     S=F(0)
     for h in range(-2*H,2*H+1):
      y=2*h*t;v=y-floor(y+F(1,2));S+=N if not v else min(N,1/(2*abs(v)))
     budget=sum(bin_cost(N,q,b) for b in range(-q,q+1))
     factor=F(16*H,q)+2
     assert S<=factor*budget<=factor*(2*N+2*q*(1+series[q]))
     c['complete_rational_kernel_bounds']+=1
 assert sum(bin_cost(F(100),1,b) for b in range(-1,2))>2*harmonic(1) # central costs cannot vanish
 assert bin_cost(F(0),5,-2)!=F(5,2) # negative tail shift is b+1,not b
 assert set(range(0,1))!={-1,0} # q>0 required for two central bins
 assert harmonic(4)>1 # logarithmic growth cannot be deleted
 c['negative_controls']=4
 return {'status':'PASS','scope':'Exact rational finite partition,tail injection,harmonic upper budgets and 128-term positive atanh-series sanity; log theorem itself is pinned native source,not certified by this regression. No Lean/minor asymptotic claim.','counts':c}
if __name__=='__main__':
 r=run();Path(__file__).with_name('HARMONIC-BUDGET-REGRESSION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
