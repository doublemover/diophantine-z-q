#!/usr/bin/env python3
from fractions import Fraction as R
from pathlib import Path
from math import isqrt
from itertools import combinations
import json
P=Path(__file__).resolve().parent.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json'
I=json.loads(P.read_text()); h=I['h']; beta=114444*I['R_input']//(17*12**2)
assert h==473592745039516333133760 and beta==204618888056724185
def prime(n):return n>1 and all(n%d for d in range(2,isqrt(n)+1))
def chi(n,p):
 a=pow(n%p,(p-1)//2,p)
 return -1 if a==p-1 else a
rows=[]
for p in range(7,325):
 if not prime(p) or beta%p==0 or (chi(beta,p),chi(-3,p))!=(-1,1):continue
 for q in range(1,p):
  if chi(q,p)!=-1:continue
  a=3*(q+1)*(4*q+3)%p; d=(3*q-1)*(4*q-1)%p
  b=-3*(4*q*q+1)%p; e=(4*q-1)*(4*q+3)%p
  if not (a*d*b*e)%p:continue
  A=beta*a*pow(d,-1,p)%p; B=beta*b*pow(e,-1,p)%p
  if (chi(A,p),chi(B,p))==(1,1):
   rows.append(dict(p=p,q=q,beta_mod_p=beta%p,betaF=A,betaG=B));break
 else:raise AssertionError(p)
assert len(rows)==15 and rows[0]['p']==13
C=[R(-1),R(-3,4),R(1,3),R(1,4)]
D=[x-y for x,y in combinations(C,2)]+[4*x*x+1 for x in C]
assert all(d and all((d.numerator*d.denominator)%p for p in range(7,40) if prime(p) and p!=13) for d in D)
def f(x,b):return (x-b)*(x+3*b)
Q=[]
for delta in [R(1,20),R(3,19),R(13,81),R(131*82)]:
 for u in [R(3,7),R(1,5),R(3,2),R(11)]:
  q=delta*u*u
  z=(12*q*q+3)/(2+7*q);z2=-3+z/q
  ff=3*(q+1)*(4*q+3)/((3*q-1)*(4*q-1)); gg=-3*(4*q*q+1)/((4*q-1)*(4*q+3))
  assert (z+3)/(z-1)==ff and (z2+3)/(z2-1)==gg
  Z=u**3*((z2-1)/(z-1))**2
  x1,x2=beta*ff,beta*delta*gg
  assert x1*f(x1,beta)==Z**2*x2*f(x2,beta*delta)
  WF=delta**4*(gg/ff)*Z**2*f(beta*gg,beta)**2 # formal square of W
  assert WF==delta*f(beta*ff,beta)*f(beta*gg,beta)
  Q.append([str(delta),str(u)])
q=R(1,4); p=R(-3,4)
assert -(q+1)*(4*q+3)**2/((3*q-1)*(4*q*q+1))==64
assert -9*(p+1)*(4*p*p+1)/((3*p-1)*(4*p-1)**2)==R(9,64)
print(json.dumps(dict(h=h,beta=beta,genus=9,total_branch_points=12,small_prime_rows=rows,
 rational_identity_specializations=Q,limits_at_positive_common_pole='64',limit_at_negative_opposite='9/64',
 scope='everywhere local literal multisection only, no Q point'),indent=2,sort_keys=True))
