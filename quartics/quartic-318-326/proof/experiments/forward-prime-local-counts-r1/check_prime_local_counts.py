#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import math,json
H=Path(__file__).resolve().parent;O=H.parent/'forward-jacobi-cm-producer-r1'
i=json.loads((O/'intake.json').read_text())
for n in i['order']:assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n
norms=0;pairs=0;quads=0;literal=0
for p in range(3,44):
 if any(p%d==0 for d in range(2,math.isqrt(p)+1)):continue
 e=1 if p%4==1 else -1
 N=[0]*p
 for a,b in product(range(p),repeat=2):N[(a*a+b*b)%p]+=1
 assert N[0]==p+(p-1)*e
 assert all(N[t]==p-e for t in range(1,p))
 norms+=p
 C=[sum(N[t]*N[(t-s)%p] for t in range(p)) for s in range(p)]
 assert all(C[s]==p**3-p+(p*p if s==0 else 0) for s in range(p))
 pairs+=p
 for k in range(1,p):
  q=sum(C[k*w*w%p] for w in range(p))
  assert q==p**4 and q-1==p**4-1
  quads+=1
  if p<=7:
   pts=[z for z in product(range(p),repeat=5) if (z[0]**2+z[1]**2-z[2]**2-z[3]**2-k*z[4]**2)%p==0]
   assert len(pts)==q and sum(any(z) for z in pts)==q-1
   literal+=len(pts)
 assert sum(C[0] for w in range(p))!=p**4 # kappa=0 is excluded for a reason.
# Characteristic two does not satisfy the asserted zero norm fiber formula.
assert sum((a*a+b*b)%2==0 for a,b in product(range(2),repeat=2))!=2+(2-1)
print(json.dumps({'copied_sources':len(i['order']),'norm_fibers':norms,'difference_fibers':pairs,
 'nonzero_kappa_quadrics':quads,'literal_quadric_points_counted':literal,
 'negative_controls':['zero_kappa','characteristic_two'],'Lean_run':False},indent=2))
