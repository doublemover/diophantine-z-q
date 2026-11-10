#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
from math import prod
import json
H=Path(__file__).resolve().parent; O=H.parent/'forward-prime-crt-assembly-r1'
if (H/'intake.json').exists():
 old=json.loads((O/'intake.json').read_text())
 for n in old['order']:assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n

def quadric(M,k):
 pairs={r:[] for r in range(M)}
 for a,b in product(range(M),repeat=2):pairs[(a*a+b*b)%M].append((a,b))
 return [(a,b,c,d,w) for w in range(M) for r in range(M)
  for a,b in pairs[r] for c,d in pairs[(r-k*w*w)%M]]
def bad(z,p,g):return any(z) and any((z[0]**2+z[1]**2+c*z[4]**2)%p==0 for c in g)
def good(z,p,g):return any(z) and not any((z[0]**2+z[1]**2+c*z[4]**2)%p==0 for c in g)
def red(z,p):return tuple(v%p for v in z)
cases=points=formulas=0
for ps in [[],[3],[5],[7],[3,5]]:
 for kap in [1,2]:
  M=prod(ps); qs=quadric(M,kap)
  locals_=[quadric(p,kap) for p in ps]
  for g in [[0,-kap],[0,-kap,2],[0,-kap,5]]:
   den=prod(p**4-1 for p in ps)
   local_b=[sum(bad(z,p,g) for z in q) for p,q in zip(ps,locals_)]
   local_g=[sum(good(z,p,g) for z in q) for p,q in zip(ps,locals_)]
   for p,b,c in zip(ps,local_b,local_g):
    assert b+c==p**4-1
    if len(set(x%p for x in g))==len(g):
     e=1 if p%4==1 else -1;nu=p+(p-1)*e;n=p-e
     formula=Q((p-1)*n*(2*nu+(len(g)-2)*n)+nu*nu-1,p**4-1)
     assert formula==Q(b,p**4-1);formulas+=1
   b=sum(all(bad(red(z,p),p,g) for p in ps) for z in qs)
   c=sum(all(good(red(z,p),p,g) for p in ps) for z in qs)
   assert b==prod(local_b) and c==prod(local_g)
   assert Q(b,den)==prod(Q(v,p**4-1) for p,v in zip(ps,local_b))
   assert Q(c,den)==prod(1-Q(v,p**4-1) for p,v in zip(ps,local_b))
   points+=len(qs);cases+=1
# Complement is taken inside primitive points, so affine-origin must not survive.
assert not good((0,0,0,0,0),5,[0,-1])
# Conditions at different primes may use different coefficient witnesses.
z=(6,0,10,10,1)
assert (z[0]**2+z[1]**2-z[2]**2-z[3]**2-z[4]**2)%15==0
assert all(bad(red(z,p),p,[0,-1]) for p in [3,5])
assert not any(all((z[0]**2+z[1]**2+g*z[4]**2)%p==0 for p in [3,5]) for g in [0,-1])
print(json.dumps({'systems':cases,'literal_points':points,'local_closed_form_matches':formulas,
 'empty_and_colliding_coefficients':True,'lean_run':False},indent=2))
