#!/usr/bin/env python3
from itertools import product
import sympy as s
import json
x,z,w=s.symbols('x z w');pairs=irreducible=exceptional=0
for k,t in product(range(-8,9),range(-8,9)):
 if not k or not t:continue
 P=k*w*w+2*t;D=(t*t+x*x)*(t*t+z*z)
 P2=k*(t+2)*w*w-2*x*z;K=(k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2
 assert s.Poly(s.gcd(P,D),x,z,w,domain=s.QQ).total_degree()==0
 assert s.Poly(s.gcd(P2,K),x,z,w,domain=s.QQ).total_degree()==0
 pairs+=2
 if t!=-2:
  fac=s.factor_list(P2,x,z,w)[1];assert len(fac)==1 and fac[0][1]==1
  assert K.subs({x:0,z:0,w:0})==t*t*(t+2)**2!=0
  irreducible+=1
 else:
  assert K.subs({x:0,z:1,w:0})==4 and K.subs({x:1,z:0,w:0})==4
  exceptional+=1
# At k=1,t=0 the actual second pair shares w²-xz.
assert s.Poly(s.gcd(2*w*w-2*x*z,(w*w-x*z)**2),x,z,w).total_degree()==2
print(json.dumps({'rational_pair_gcd_checks':pairs,'regular_irreducible_quadratics':irreducible,'exceptional_minus_two_cases':exceptional,'zero_slice_negative_control':'PASS'},sort_keys=True))
