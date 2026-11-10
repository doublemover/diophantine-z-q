#!/usr/bin/env python3
"""Finite exact checks, never a replacement for universal CM or Lean."""
from pathlib import Path
import hashlib,json,math
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'forward-conjugate-count-selection-r2'
old=json.loads((OLD/'intake.json').read_text())
for n in old['order']:
 assert (HERE/(n+'.lean')).read_bytes()==(OLD/(n+'.lean')).read_bytes(),n

def prime(p):return p>1 and all(p%d for d in range(2,math.isqrt(p)+1))
def chi(p,x):
 r=pow(x%p,(p-1)//2,p)
 return -1 if r==p-1 else r
def trace(p,D):return sum(chi(p,x*x*x-D*x) for x in range(p))
scalings=0;counts=0;cm=0
for p in range(3,72):
 if not prime(p):continue
 sums=[trace(p,D) for D in range(p)]
 for D in range(p):
  for c in range(1,p):
   assert sums[D*c*c%p]==chi(p,c)*sums[D]
   scalings+=1
 for c in range(1,p):
  assert sums[c*c%p]**2==sums[1]**2
  counts+=1
for p in range(5,500):
 if not prime(p) or p%4!=1:continue
 s=trace(p,1)
 for a in range(-math.isqrt(p),math.isqrt(p)+1):
  for b in range(-math.isqrt(p),math.isqrt(p)+1):
   if a*a+b*b!=p or a%2!=1 or b%2!=0:continue
   assert s*s==4*a*a
   for c in range(1,min(p,25)):
    n=p+1+trace(p,c*c)
    assert n in ((a-1)**2+b*b,(a+1)**2+b*b)
   cm+=1
# Excluded zero scaling and wrong Gaussian-associate parity really matter.
assert trace(5,0)**2!=trace(5,1)**2
assert 2*2+1*1==5 and trace(5,1)**2!=4*2*2
print(json.dumps({'unchanged_sources':len(old['order']),'exact_scalings':scalings,
 'trace_square_cases':counts,'signed_odd_real_CM_samples':cm,
 'negative_controls':['zero scale','wrong Gaussian associate parity'],
 'universal_CM_proved':False,'Lean_run':False},indent=2))
