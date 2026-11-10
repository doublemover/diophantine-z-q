#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
import json
H=Path(__file__).resolve().parent;O=H.parent/'forward-prime-local-density-r2'
i=json.loads((O/'intake.json').read_text())
for n in i['order']:assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n
cases=0
qs=[Q(n) for n in range(2,101)]+[Q(101,100),Q(3,2),Q(11,10)]
for q in qs:
 for k in range(21):
  for e in [-1,1]:
   nu=q+(q-1)*e
   g=((q-1)*(q-e)*(2*nu+(k-2)*(q-e))+nu*nu-1)/(q**4-1)
   R=(2*e+1)*k*q*q+2*e*(q+1)+k
   D=q*(q+1)*(q*q+1)
   assert g-(k+2*e)/q==-R/D
   assert abs(R)<=4*(k+1)*q*q
   assert q**4<=D
   assert abs(g-(k+2*e)/q)<=4*(k+1)/(q*q)
   cases+=1
print(json.dumps({'unchanged_sources':len(i['order']),'exact_rational_cases':cases,
 'includes_near_one':True,'constant':'4(k+1)','Lean_run':False},indent=2))
from itertools import permutations
import sympy
outside=0;systems=0
for kap in [-7,-3,-1,1,3,7]:
 for extras in [[],[2],[2,5],[-11,2,5]]:
  gam=list(dict.fromkeys([0,-kap,*extras]))
  P=2*abs(kap)
  for a,b in permutations(gam,2):P*=abs(b-a)
  assert P>0
  exceptional=set(sympy.factorint(P))
  for p in sympy.primerange(2,102):
   if p in exceptional:continue
   assert p!=2 and kap%p and len({g%p for g in gam})==len(gam)
   outside+=1
  systems+=1
assert 5 not in {2} and len({0%5,5%5})!=2
print(json.dumps({'fixed_integer_systems':systems,'outside_prime_applications':outside,
 'negative_control':'omitting coefficient differences permits residue collisions'},indent=2))
