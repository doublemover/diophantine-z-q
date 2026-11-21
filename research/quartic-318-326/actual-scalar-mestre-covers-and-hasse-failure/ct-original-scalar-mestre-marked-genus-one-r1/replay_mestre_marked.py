#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
import json
P=Path(__file__).resolve().parent.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json'
R=json.loads(P.read_text())
beta=114444*R['R_input']//(17*12**2)
assert beta==204618888056724185
primes=(131,6551,2470991,16782959)
for p in primes:
 assert all(p%n for n in range(2,isqrt(p)+1)) and pow(5,(p-1)//2,p)==1
def f(x,b): return (x-b)*(x+3*b)
gdef=lambda x,n:x*f(x,n)
rows=[]
for d in [F(1,20), F(3,19), F(13,81), F(131*82)]:
 for u in [F(3,2),F(11),F(1,5),F(23,7)]:
  q=d*u*u
  X0=beta*(1-4*q)/5; X1=beta*d*(1-4/q)/5
  assert X0-beta==u*u*(X1-beta*d)
  assert gdef(X0,beta)==u**6*gdef(X1,beta*d)
  s=beta*(X0+3*beta)/(X0-beta)
  t=X1/d
  assert s==beta*(q-4)/(q+1) and t==beta*(q-4)/(5*q)
  Bsq=(q+1)/(5*d)
  Wsq=16*beta**4*Bsq*(4*q-1)**2/(u**4*(q+1)**2)
  assert d*f(s,beta)*f(t,beta)==Wsq
  a2=F(beta,5)*(u*u-4/d);b2=(u*u+1/d)/5
  assert a2/b2==s and a2/(u*u)==t
  xd=beta*d*d*u*u
  assert xd-4*beta*d==5*d*d*a2 and xd+beta*d==5*beta*d*d*b2
  assert xd*(xd-4*beta*d)*(xd+beta*d)==(5*beta*d**3*u)**2*a2*b2
  rows.append([str(d),str(u)])
# Synthetic rational calibration of the reverse map, not a Ready pole.
b,d,u,A,B=29,F(1,20),F(15),F(29),F(7)
q=d*u*u
assert A*A==F(b,5)*(u*u-4/d) and 5*B*B==u*u+1/d
t,t1,W=A/B,A/u,4*b*b*B*(4*q-1)/(u*u*(q+1))
assert W*W==d*f(t*t,b)*f(t1*t1,b)
assert F(16*21**3,25)==F(148176,25)
print(json.dumps(dict(h=R['h'],beta=beta,known_theta_split_5=[[p,p%5] for p in primes],
 symbolic_identity_specializations=rows,synthetic_non_ready_rational_map=[str(x) for x in (t,t1,W)],
 j='148176/25',ordered_mark=['beta',5,'5*beta'],scope='new exact literal sufficient marked curve; local sqrt5 norm gate unproved on unseen support; no rational point'),indent=2,sort_keys=True))
