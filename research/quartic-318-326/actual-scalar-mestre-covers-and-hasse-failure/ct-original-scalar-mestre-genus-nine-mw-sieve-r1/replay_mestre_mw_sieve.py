#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
import json
I=json.loads((Path(__file__).resolve().parent.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json').read_text())
B=114444*I['R_input']//(17*12**2)
assert B==204618888056724185 and B%17==0 and B%(17*17)!=0
def i(a,b,p):
 if p:return (a*pow(b,-1,p))%p
 return F(a,b)
def plus(P,Q,p=None):
 if P is None:return Q
 if Q is None:return P
 x,y=P;a,b=Q
 if x==a and ((y+b)%p if p else y+b)==0:return None
 m=i(3*x*x-4*x+65,2*y,p) if P==Q else i(b-y,a-x,p)
 X=m*m+2-x-a; Y=m*(x-X)-y
 return (X%p,Y%p) if p else (X,Y)
def mult(n,p):
 P=(5%p,20%p) if p else (5,20)
 s=None
 for _ in range(n):s=plus(s,P,p)
 return s
assert mult(2,None)==(1,-8) and mult(4,None)==(16,68)
assert mult(8,None)[0]==F(191**2,136**2)
for n in [1,2,3,4,8]:
 x,y=mult(n,None)
 if x==-15:continue
 q=(5-x)/(x+15)
 z=F(1)/(q+1)
 w=y/(20*z*z)
 assert x==20*z-15 and w*w==-(q+1)*(3*q-1)*(4*q*q+1)
count=lambda p:1+sum((y*y-x*(x*x-2*x+65))%p==0 for x in range(p) for y in range(p))
assert [count(p) for p in [3,11]]==[6,10]
assert mult(4,17)==(16,0) and mult(8,17) is None
assert mult(7,131)==(0,0) and mult(2,131) is not None and mult(14,131) is None
roots17=list(q for q in range(17)
  if ((q+1)*(4*q+3)*(3*q-1)*(4*q-1))%17==0 and ((4*q*q+1)*(4*q-1)*(4*q+3))%17==0)
assert set(roots17)=={pow(4,-1,17),(-3*pow(4,-1,17))%17}
assert [q for q in roots17 if pow(q,8,17)==1]==[pow(4,-1,17)]
assert pow(B%131,65,131)==1 and pow(-3%131,65,131)==130
D0=1+114444*I['R_input'];c=12*pow(D0,-1,131**2)%(131**2) # verified literal Wsrc≡1
assert (1-B*c*c)%131**2==82*131
squares8={z*z%8 for z in range(8)}
assert all((2*k**4+k*k*s*s-8*s**4)%8 not in squares8 for k in range(1,8,2) for s in range(1,8,2))
assert all((8*l**4+l*l*s*s-2*s**4)%8 not in squares8 for l in range(8) for s in range(1,8,2))
print(json.dumps(dict(h=I['h'],beta=B,rank_Estar=1,class_alpha=[1,5,13,65],class_alpha_dual=[-1,1],
 torsion_primes_and_counts=[[3,6],[11,10]],at17=dict(order_P=8,nonzero_P4=[16,0],shared_residues=roots17,allowed_q=pow(4,-1,17),epsilon=0,n_mod_two=0),
 at131=dict(order_P=14,P7=[0,0],delta_residue=82*131,allowed_q=0,n_mod_two=1),
 scope='actual genus9 branch only; no global rational point, still locally soluble'),indent=2,sort_keys=True))
