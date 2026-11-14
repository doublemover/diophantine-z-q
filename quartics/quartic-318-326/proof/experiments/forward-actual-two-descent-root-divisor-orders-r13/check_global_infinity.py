#!/usr/bin/env python3
"""Exact global-factor Bezout/root-product identities and rational original-chart unit checks, not Lean or scheme descent."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
c=dict(bezout_syzygy=0,root_product_syzygy=0,original_chart_points=0,global_root_units=0)
for u,v,b in product(map(F,range(-3,4)),repeat=3):
 f=1+u*b;g=1-u*b+u*u*b*b-v*b**3
 assert f*g-1==-b**3*(v*f-u**3);c['bezout_syzygy']+=1
for n,u,e in product(map(F,range(-3,4)),repeat=3):
 d1=1-n*e*u*u;d2=1+3*n*e*u*u
 assert u**3*(d1*d2-e)==u*(u-n*e*u**3)*(u+3*n*e*u**3)-e*u**3
 c['root_product_syzygy']+=1
for t in [F(i,j) for i in range(-5,6) if i for j in (1,2,3)]:
 for n,x,y in [(t*t,3*t*t,6*t**3),(F(0),t*t,t**3)]:
  assert y*y==x*(x-n)*(x+3*n)
  u,v=x/y,1/y;b=-2*n*u+3*n*n*v;f=1+u*b;g=1-u*b+u*u*b*b-v*b**3
  assert f*g==1;assert v==g*u**3;c['original_chart_points']+=1
  for a in (0,n,-3*n):
   d=1-a*g*u*u
   assert d!=0;assert u-a*v==u*d;assert (x-a)*u*u==d/g
   c['global_root_units']+=1
r={'status':'PASS','scope':__doc__,'checks':c};Path(__file__).with_name('GLOBAL-INFINITY-REGRESSION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
