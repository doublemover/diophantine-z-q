#!/usr/bin/env python3
"""Exact rational overlap syzygies and inverse-coordinate checks, not quotient-ring or Lean validation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
c=dict(affine_syzygy=0,infinity_syzygy=0,affine_roundtrip=0,infinity_roundtrip=0,root_numerator=0)
for n,x,y,z in product(map(F,range(-2,3)),repeat=4):
 h=y*y-x**3-2*n*x*x+3*n*n*x;i=y*z-1
 t=z-(x*z)**3-2*n*(x*z)**2*z+3*n*n*(x*z)*z*z
 assert t==z**3*h-z*(y*z+1)*i;c['affine_syzygy']+=1
 h=y-x**3-2*n*x*x*y+3*n*n*x*y*y;i=y*z-1
 t=z*z-(x*z)**3-2*n*(x*z)**2+3*n*n*x*z
 assert t==z**3*h-(z*z*(1-2*n*x*x)+3*n*n*x*z*(y*z+1))*i;c['infinity_syzygy']+=1
for x,y in product(map(F,range(-5,6)),repeat=2):
 if not y:continue
 u,v=x/y,1/y
 assert (u/v,1/v)==(x,y);c['affine_roundtrip']+=1
 u,v=x,y
 X,Y=u/v,1/v
 assert (X/Y,1/Y)==(u,v);c['infinity_roundtrip']+=1
 for a in map(F,range(-3,4)):
  assert X-a==(u-a*v)/v;c['root_numerator']+=1
r={'status':'PASS','scope':__doc__,'checks':c};Path(__file__).with_name('OVERLAP-REGRESSION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
