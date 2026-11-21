#!/usr/bin/env python3
from math import prod
import sympy as s
v=s.symbols('v')
D=2811626664334219040035976315
old=(5,11,17,163,661,733,1489,1861,114649,119851)
assert D==prod(old) and all(s.isprime(p) for p in old)
f=3*v**4+8*v**3-18*v**2-9
g=s.Poly(v**4+v**3-v**2+2,v,modulus=5)
assert s.Poly(2*f,v,modulus=5)==g
assert g.gcd(s.Poly(v**25-v,v,modulus=5)).degree()==0
fm=s.Poly(27*f.subs(v,v/3).expand(),v)
assert fm.as_expr()==v**4+8*v**3-54*v**2-243
assert s.discriminant(fm)==-2**16*3**13
assert s.resultant(f,v*(v-1)*(v+3),v)//27==-768
p=13
assert D%p==1
c=1+sum(y*y%p==x*(x-D)*(x+3*D)%p for x in range(p) for y in range(p))
assert c==16 and p+1-c==-2
m=97*15527
assert m==1506119 and m%13==4 and m%24==23 and all(pow(-m%p,(p-1)//2,p)==1 for p in (*old,13))
assert all(D%p for p in (97,15527)) and all(s.isprime(p) for p in (97,15527))
print('degree 8 tame factor digits',len(str(D**4)))
print('degree 168 tame factor digits',len(str(D**84)))
print('13 ordinary count',c,'a13',p+1-c)
