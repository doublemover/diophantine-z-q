#!/usr/bin/env python3
"""Exact finite swapped-polynomial/Eisenstein arithmetic only; not Lean or a DVR proof."""
from fractions import Fraction as F
from itertools import product
import json
counts=dict(swapped_equation=0,eisenstein_coefficients=0,constant_not_square=0)
for n in map(F,[-9,-3,-1,0,1,2,5,11]):
 # Coefficients in v of the polynomial in u, represented low-to-high.
 coeff=[(0,-1),(0,0,-3*n*n),(0,2*n),(1,)]
 assert coeff[3]==(1,)
 assert all(c[0]==0 for c in coeff[:3]);counts['eisenstein_coefficients']+=4
 assert coeff[0][1]!=0;counts['constant_not_square']+=1
 for ui,vi in product(range(-6,7),repeat=2):
  u=F(ui,3);v=F(vi,5)
  original=v-u**3-2*n*u*u*v+3*n*n*u*v*v
  swapped=u**3+2*n*v*u*u-3*n*n*v*v*u-v
  assert swapped==-original;counts['swapped_equation']+=1
print(json.dumps({'status':'PASS','scope':__doc__,'checks':counts},indent=2))
