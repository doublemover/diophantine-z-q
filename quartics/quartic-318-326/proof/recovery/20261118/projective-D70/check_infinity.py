#!/usr/bin/env python3
"""Small exact arithmetic checks supplementing, not proving, the source argument."""
from itertools import product
from pathlib import Path
import re
F=Path(__file__).with_name('inputs')/'OriginalIntegerAffineModel318.lean'
C=list(map(int,re.search(r'def contacts : Fin 4 → ℤ := !\[([^\]]+)\]',F.read_text())[1].split(',')))
def d(s):
 z=1
 for c in C[1:]: z*=1-c*s
 return z
assert d(0)==1
assert (d(2)%3)==0 and 2*2%3==1
# CRT of w_i²-1 uses eight sign points, and the 8x8 Hadamard
# evaluation matrix in the monomial basis is invertible after inverting 2.
vs=list(product([-1,1],repeat=3))
ex=list(product([0,1],repeat=3))
M=[[v[0]**e[0]*v[1]**e[1]*v[2]**e[2] for e in ex] for v in vs]
assert all(sum(a*b for a,b in zip(M[i],M[j]))==8*(i==j) for i in range(8) for j in range(8))
print('PASS: actual contacts, d(0)=1, collision excluded by d, sign-section CRT matrix')
