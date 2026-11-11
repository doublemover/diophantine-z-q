#!/usr/bin/env python3
import itertools,json
C=dict(finite_torsion_groups=0,free_finite_rank_cases=0,exact_obstruction_equations=0,subgroup_embeddings=0,actual_quotient_cosets=0)
for a,b,m in itertools.product(range(1,6),range(1,6),[1,3,5,7,9]):
 mods=[2**a,2**b,m]
 kernel=1
 for q in mods:kernel*=sum(2*x%q==0 for x in range(q))
 assert kernel==4;C['finite_torsion_groups']+=1
 for r in [0,1]:
  quotient=2**r*kernel;obs=8//quotient
  assert quotient*obs==8 and 2**r*obs==2
  assert (r==0 and quotient==4 and obs==2) or(r==1 and quotient==8 and obs==1)
  C['free_finite_rank_cases']+=1;C['exact_obstruction_equations']+=1
V=set(range(8))
for r in [2,3]:
 for basis in itertools.product(range(1,8),repeat=r):
  image=set()
  for coeff in itertools.product([0,1],repeat=r):
   z=0
   for c,b in zip(coeff,basis):
    if c:z^=b
   image.add(z)
  if len(image)!=2**r:continue
  cosets={frozenset(x^a for a in image) for x in V}
  assert len(image)*len(cosets)==8
  assert len(cosets)==(2 if r==2 else 1)
  assert (all(frozenset(x^a for a in image)==image for x in V))==(r==3)
  C['subgroup_embeddings']+=1;C['actual_quotient_cosets']+=len(cosets)
print(json.dumps({'status':'PASS','checks':C,'scope':'Finite torsion doubling/index calculations and actual finite coset quotients model the exact source identities. No choice of the rank-one alternative or global point-existence inference.'},indent=2))
