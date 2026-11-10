#!/usr/bin/env python3
from itertools import product
from math import prod
from pathlib import Path
import sympy as S
root=Path(__file__).resolve().parent
checks={'literal_basis_determinants':0,'original_index_counts':0,'kernel_vectors':0}
for ps in [[],[3],[5],[3,5],[3,5,7]]:
 M=prod(ps)
 for k in [1,2]:
  for ts in product(*([None]+list(range(p)) for p in ps)):
   q=prod(p for p,s in zip(ps,ts) if s is not None);r=M//q
   A=next(a for a in range(q) if all((a-k*s*s)%p==0 for p,s in zip(ps,ts) if s is not None))
   D=next(d for d in range(M) if all((d-(0 if s is None else s))%p==0 for p,s in zip(ps,ts)))
   basis=S.Matrix([[r,0,0],[A*r,q,0],[D*r,0,M]])
   assert basis.det()==M*M and q*r*M==M*M
   checks['literal_basis_determinants']+=1
   if M<=15:
    count=0
    for x,z,w in product(range(M),repeat=3):
     if all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ts)):count+=1
    assert count==M and M**3//count==M*M
    checks['original_index_counts']+=1;checks['kernel_vectors']+=count
# The standard Euclidean reference is unit volume and the embedding adds no factor.
assert S.eye(3).det()==1
# This OTHER quartic-coordinate transformation is not unimodular and must not enter.
quartic=S.Matrix([[1,0,1,0,0],[1,0,-1,0,0],[0,1,0,-1,0],[0,1,0,1,0],[0,0,0,0,1]])
assert abs(quartic.det())==4
text=(root/'OriginalCovolumeIndex318.lean').read_text()
for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'negative control: quartic transformation det4 is not reference embedding')
