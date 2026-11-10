#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from pathlib import Path
import sympy as S
root=Path(__file__).resolve().parent
checks={'integer_norm_gap':0,'dual_norm_gap':0,'modulus_axis_spans':0,'coordinate_expansions':0}
for v in product(range(-7,8),repeat=3):
 norm2=sum(x*x for x in v)
 assert (norm2<1)==(v==(0,0,0))
 checks['integer_norm_gap']+=1
 for M in [1,3,5,15,105]:
  w=tuple(Q(x,M) for x in v)
  assert (sum(x*x for x in w)<Q(1,M*M))==(v==(0,0,0))
  checks['dual_norm_gap']+=1
for M in range(1,51):
 axes=S.diag(M,M,M)
 assert axes.det()==M**3 and axes.rank()==3
 assert axes*S.diag(Q(1,M),Q(1,M),Q(1,M))==S.eye(3)
 checks['modulus_axis_spans']+=1
for v in product(range(-3,4),repeat=3):
 w=tuple(Q(x,7) for x in v)
 axes=[(1,0,0),(0,1,0),(0,0,1)]
 assert tuple(sum(w[i]*axes[i][j] for i in range(3)) for j in range(3))==w
 checks['coordinate_expansions']+=1
# A uniform radius1 for the dual is false; the ORIGINAL modulus matters.
assert Q(1,15)**2<1 and Q(1,15)!=0
for name in ['OriginalFullEuclideanLattice318','OriginalFullDualLattice318']:
 text=(root/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'negative control: dual radius cannot be replaced by1')
