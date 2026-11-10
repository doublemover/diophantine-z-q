#!/usr/bin/env python3
from itertools import product,combinations
from math import prod
from pathlib import Path
root=Path(__file__).resolve().parent
checks={'multiple_boxes':0,'weighted_exception_sums':0,'incidence_sums':0,'short_dual_families':0,'zero_subset_divisibility':0}
def vecs(B): return [v for v in product(range(-B,B+1),repeat=3) if v!=(0,0,0)]
def dirs(p,k,v):
 a,b,c=v
 return [s for s in range(p) if (a+b*k*s*s+c*s)%p==0]+([None] if b%p==0 else [])
for B in range(10):
 vs=vecs(B)
 for d in range(1,25):
  count=sum(all(x%d==0 for x in v) for v in vs)
  assert d*count<=27*B**3
  if d>B: assert count==0
  else: assert count<= (2*B//d+1)**3 and count*d**3<=27*B**3
  checks['multiple_boxes']+=1
for ps in [[],[3],[5],[3,5],[3,7],[3,5,7]]:
 n=len(ps)
 for B in range(7):
  vs=vecs(B)
  zs=[]
  for v in vs:
   zero=[p for p in ps if all(x%p==0 for x in v)]
   d=prod(zero)
   assert all(x%d==0 for x in v)
   major=sum(prod(s) for r in range(n+1) for s in combinations(ps,r) if all(x%prod(s)==0 for x in v))
   assert d<=major
   zs.append(d);checks['zero_subset_divisibility']+=1
  assert sum(zs)<=2**n*27*B**3
  checks['weighted_exception_sums']+=1
  for k in [1,2,4,8]:
   counts=[prod(len(dirs(p,k,v)) for p in ps) for v in vs]
   assert all(c<=2**n*d for c,d in zip(counts,zs))
   assert sum(counts)<=27*4**n*B**3
   checks['incidence_sums']+=1
   if B<=3:
    family=set()
    for v in vs: family.update(product(*(dirs(p,k,v) for p in ps)))
    assert len(family)<=sum(counts)<=27*4**n*B**3
    checks['short_dual_families']+=1
# The excluded zero vector is essential, not a cosmetic hypothesis.
assert prod(len(dirs(p,1,(0,0,0))) for p in [3,5])==24>27*4**2*0**3
# Repeated primes cannot be silently folded into the actual CRT divisibility.
assert all(3%x==0 for x in [3,3]) and 3%prod([3,3])!=0
for file in ['NonzeroMultipleBox318.lean','OriginalBoundedDualSum318.lean','OriginalShortDualLattices318.lean']:
 text=(root/file).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']: assert bad not in text,(file,bad)
print('PASS',checks,'negative controls: zero vector; repeated prime product')
