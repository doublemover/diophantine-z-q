#!/usr/bin/env python3
"""Exact truncated rational chart algebra only; not Lean, DVR, divisor or theta/Weil identification."""
from fractions import Fraction as F
import json
counts=dict(chart_coefficients=0,unit_coefficients=0,root_numerator_coefficients=0,pole_unit_coefficients=0,overlap_identities=0)
def add(a,b):return [x+y for x,y in zip(a,b)]
def neg(a):return [-x for x in a]
def scale(c,a):return [c*x for x in a]
def mul(a,b):
 N=len(a);return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(N)]
def inverse(a):
 N=len(a);b=[F(0)]*N;b[0]=1/a[0]
 for k in range(1,N):b[k]=-sum(a[j]*b[k-j] for j in range(1,k+1))/a[0]
 return b
for n in map(F,[-5,-1,0,1,3,7]):
 for N in [8,12,20]:
  z=[F(0)]*N;one=z[:];one[0]=1;u=z[:];u[1]=1;u2=mul(u,u);u3=mul(u2,u)
  v=z[:]
  for _ in range(N):v=add(u3,add(scale(2*n,mul(u2,v)),scale(-3*n*n,mul(u,mul(v,v)))))
  factor=add(one,add(scale(-2*n,u2),scale(3*n*n,mul(u,v))))
  assert mul(v,factor)==u3;counts['chart_coefficients']+=N
  e=inverse(factor);assert mul(v,factor)==u3 and e[0]==1
  counts['unit_coefficients']+=N
  for a in [0,n,-3*n,F(2,3),F(-7,2)]:
   d=add(one,scale(-a,mul(e,u2)))
   assert add(u,scale(-a,v))==mul(u,d)
   assert d[0]==1;counts['root_numerator_coefficients']+=N
   normalized=mul(d,inverse(e))
   assert normalized==add(factor,scale(-a,u2))
   assert normalized[0]==1;counts['pole_unit_coefficients']+=N
 for ui in range(-4,5):
  for vi in [-3,-1,1,2,5]:
   u=F(ui,3);v=F(vi,2)
   chart=v-u**3-2*n*u*u*v+3*n*n*u*v*v
   affine=(1/v)**2-(u/v)*(u/v-n)*(u/v+3*n)
   assert affine*v**3==chart
   counts['overlap_identities']+=1
print(json.dumps({'status':'PASS','scope':__doc__,'checks':counts},indent=2))
