#!/usr/bin/env python3
"""Exact supporting identities; not a substitute for the Lean induction."""
from itertools import product
import runpy
from pathlib import Path
ns=runpy.run_path(str(Path(__file__).with_name('check_order.py')))
s=ns['s'];mul=ns['mul'];star=ns['star']
for r,i,j,k in product(range(3),repeat=4):
    if (r*r+210*i*i-5*j*j-1050*k*k)%3==0:assert r==j==0
    if (3*r*r+70*i*i-15*j*j-350*k*k)%3==0:assert i==k==0
r,i,j,k=s.symbols('r i j k');x=s.Matrix([r,i,j,k]);N=r*r+210*i*i-5*j*j-1050*k*k
for z in (mul(x,star(x)),mul(star(x),x)):
    assert all(s.expand(a-b)==0 for a,b in zip(z,s.Matrix([N,0,0,0])))
print('PASS: both full mod3 residue tables, both literal norm identities; induction/denominator bridge remains for hosted Lean')
