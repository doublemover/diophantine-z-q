#!/usr/bin/env python3
"""Exact rational coordinate regression, not a Lean/analytic proof."""
from fractions import Fraction as F
from itertools import product
import json
counts={'finite_infinity_overlap':0,'infinity_signs':0,'negative_wrong_scale':0}
for r0,r1,s in [(5,3,4),(13,5,12),(17,8,15),(25,7,24)]:
 for r2 in [-9,-2,1,4,11]:
  for m in [-7,-1,2,6]:
   for t in [-3,0,5]:
    a,b,c=F(t-r0*r0),F(t-r1*r1),F(t-r2*r2)
    d=b-a;l=(c-a)/d;shift=(1+l)/3;center=a+d*shift
    A=-(l*l-l+1)/3;B=-(2*l-1)*(l-2)*(l+1)/27
    x=(F(t)-center)/d;y=F(r0*r1*r2,s**3)
    assert y*y==x**3+A*x+B
    u=F(1,m);D=F(r0*r1*r2,m**3);o=F(t-m*m)
    U=s*u*(1+(o-center)*u*u)/D;V=s**3*u**3/D
    assert U==x/y and V==1/y
    assert V-U**3-A*U*V**2-B*V**3==0
    assert U/V==x and 1/V==y
    counts['finite_infinity_overlap']+=1
    if x:
     assert U!=2*x/y
     counts['negative_wrong_scale']+=1
for signs in product([-1,1],repeat=3):
 D=signs[0]*signs[1]*signs[2];assert D!=0
 u=0;assert 4*u*(1+3*u*u)/D==0 and 4**3*u**3/D==0
 counts['infinity_signs']+=1
print(json.dumps({'status':'PASS','exact_rational':True,'scope':'Coordinate identities and zero-parameter coverage only; no topology or Lean acceptance','counts':counts},indent=2))
