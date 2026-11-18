"""Independently exhaust small nonzero quadrics, bad pairs and sieve density using norm fibres."""
from itertools import product
from collections import Counter
from fractions import Fraction
from math import prod
from sympy import symbols,expand
from pathlib import Path
import json
def test(p,kap,gamma):
 c=Counter((x*x+y*y)%p for x in range(p) for y in range(p));chi=1 if p%4==1 else -1
 good=bad=0
 n0=c[0]
 for w in range(p):
  for v in range(p):
   n=c[v]*c[(v-kap*w*w)%p]
   good+=n
   if any((v+g*w*w)%p==0 for g in gamma):bad+=n
 assert good==p**4
 assert bad-1==(p-1)*(p-chi)*(2*n0+(len(gamma)-2)*(p-chi))+n0*n0-1
 for e1,e2 in product([-1,1],repeat=2):
  n=0
  A=Counter((a*a+b*b)%p for a,b in product(range(p),repeat=2)if ((a+e1)**2+b*b)%p==0)
  B=Counter((a*a+b*b)%p for a,b in product(range(p),repeat=2)if ((a+e2)**2+b*b)%p==0)
  for w in range(p):
   for i,n1 in A.items():n+=n1*B[(i-kap*w*w)%p]
  assert n==(1 if chi==-1 else n) and n<=4*p*p
def ident():
 w,x,z,t,kap=symbols("w x z t k");R=kap*w*w-x*z;K=(R+t*t+2*t)**2 + (t*(x+z))**2;P=kap*w*w+2*t
 assert expand(K-(t*t+x*x)*(t*t+z*z)-P*(P+2*t*t-2*x*z))==0
 Q=kap*(t+2)*w*w-2*x*z
 assert expand(Q-(t*kap*w*w+2*R))==0
 a=(R/t+t)/2; b=(x+z)/2; assert expand(4*t*t*((a+1)**2+b**2)-K)==0
ident()
count=0
for p in [5,7,11,13,17,19,23,29,31]:
 for k in [1,2,-3]:
  for gamma in [[0,-k],[0,-k,4],[0,-k,4,5]]:
   if len(set(g%p for g in gamma))!=len(gamma):continue
   test(p,k,gamma);count+=1
print(json.dumps({'sieve_density_cases':count,'sign_pairs_per_case':4}))
