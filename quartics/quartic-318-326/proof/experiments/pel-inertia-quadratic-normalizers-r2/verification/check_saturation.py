#!/usr/bin/env python3
from itertools import product
import runpy
from pathlib import Path
ns=runpy.run_path(str(Path(__file__).with_name('check_order.py')))
s=ns['s'];T=ns['T'];H=ns['H']
for p in [2,3,7]:
 for b,d in product(range(p),repeat=2):
  if (-b*b+5*b*d-5*d*d)%p==0:assert b==d==0
for a,b,c in product(range(5),repeat=3):
 if (42*a*a+42*a*c-b*b-42*c*c)%5==0:assert b==0 and (a-2*c)%5==0
a,b,c,d=s.symbols('a b c d');v=s.Matrix([a,b,c,d]);r,i,j,k=T*H.inv()*v
F=42*a*a+42*a*c-b*b+5*b*d-42*c*c-5*d*d
assert s.expand(210*(r*r+210*i*i-5*j*j-1050*k*k)-F)==0
A,B,D=s.symbols('A B D');z=s.Matrix([c+3*A,2*B-D,-A,-5*B+2*D])
assert all(s.expand(q)==0 for q in T*z-(T*H.inv()*v).subs({a:2*c+5*A,b:210*B,d:42*D}))
print('PASS: all187 local residue cases; exact inverse trace Gram, norm numerator and original lattice reconstruction')
