#!/usr/bin/env python3
"""Finite original max-norm lattice checks, not Lean/kernel tests."""
from itertools import product
from fractions import Fraction
from pathlib import Path
import json
pts=list(product(range(-2,3),repeat=5))
shells={n:sum(max(map(abs,z))==n for z in pts) for n in range(3)}
assert shells=={0:1,1:242,2:2882}
for n in range(1,201):
    shell=(2*n+1)**5-(2*n-1)**5
    assert shell==160*n**4+80*n**2+2
    assert Fraction(shell,n**6)<=Fraction(242,n*n)
for n in range(2,201):assert Fraction(1,n*n)<=Fraction(1,n*(n-1))
for i in range(5):
    v=tuple(int(j==i) for j in range(5));assert max(map(abs,v))==1
out={'status':'PASS','original_vectors':len(pts),'shell_counts':shells,'shell_bounds_checked':200,'telescoping_tail_comparisons_checked':199,'rank':5,'decay_exponent':6,'zero_frequency':'excluded from inverse-power bound and retained as one finite exception','scope':'Finite exact regression only; no Lean, infinite-series or Fourier identity acceptance.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(pts),'vectors,200 shells,199 tail inequalities')
