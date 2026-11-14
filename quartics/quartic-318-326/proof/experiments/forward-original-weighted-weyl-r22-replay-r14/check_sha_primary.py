from itertools import product
from fractions import Fraction
import json
counts=dict(finite_primary_groups=0,power_level_elements=0,sharp_cyclic_levels=0,hom_fiber_encodings=0,square_root_cases=0,alternating_cyclic_pairings=0,compatible_divisible_towers=0)
for dim in range(1,4):
 for es in product(range(1,5),repeat=dim):
  mods=tuple(2**e for e in es);G=list(product(*(range(m) for m in mods)))
  two=[x for x in G if all(2*a%m==0 for a,m in zip(x,mods))]
  assert len(two)==2**dim
  for k in range(7):
   lev=[x for x in G if all(2**k*a%m==0 for a,m in zip(x,mods))]
   assert len(lev)==2**sum(min(k,e) for e in es)
   counts['power_level_elements']+=len(lev)
   if len(two)<=2:
    assert len(lev)<=2**k
    counts['sharp_cyclic_levels']+=1
  counts['finite_primary_groups']+=1
for m in range(1,8):
 N=2**m
 for multiplier in range(N):
  f=lambda x:multiplier*x%N
  reps={}
  for x in range(N):reps.setdefault(f(x),x)
  encoded=[(f(x),(x-reps[f(x)])%N) for x in range(N)]
  assert len(set(encoded))==N
  assert all(f(k)==0 for _,k in encoded)
  counts['hom_fiber_encodings']+=N
 for k in range(m):
  for x in range(N):
   if 2**k*x%N:continue
   assert x%2==0 and 2*(x//2)%N==x
   counts['square_root_cases']+=1
 for c in range(N):
  alternating=all(c*x*x%N==0 for x in range(N))
  if alternating:
   assert c==0
   assert all(c*x*y%N==0 for x,y in product(range(N),repeat=2))
  counts['alternating_cyclic_pairings']+=1
# Actual dyadic torsion in Q/Z has finite cyclic levels but is not a finite group.
for a in range(1,16):
 for e in range(1,7):
  x=Fraction(a,2**e)%1
  tower=[x/Fraction(2**k) for k in range(12)]
  assert all((2*tower[k+1]-tower[k])%1==0 for k in range(11))
  assert all((2**k*tower[k]-x)%1==0 for k in range(12))
  counts['compatible_divisible_towers']+=1
print(json.dumps({'status':'PASS','scope':'Exact finite abelian2-group/fiber/root/pairing and rational dyadic-tower regressions; not Lean or Cassels-Tate verification','counts':counts},sort_keys=True,indent=2))
