"""Finite checks of identities and residue cases. No global rational lifting test."""
from fractions import Fraction as Q
from math import gcd,isqrt
import json
def primes(N):
 return [q for q in range(5,N+1) if all(q%i for i in range(2,isqrt(q)+1))]
def run():
 affine=0;prec=0;integer=0
 for p in primes(83):
  S={a*a%p for a in range(p)}
  for B in range(1,p):
   if B in S:continue
   for u in range(1,p):
    R=B*u*u%p;D=(1-R)%p
    if D in S:continue
    assert R not in (0,1,p-3) and 4*D%p and 36*D%p
    integer+=1
    assert any(B*(R*l*l-2*l+1)*(R*l*l+6*l+9)%p in S for l in range(p))
   assert (1-9)%p!=0
   assert any(B*(B*l*l+1)*(B*l*l+9)%p in S for l in range(p))
   prec+=1
 for i in range(1,20):
  for j in range(i+1,22):
   if gcd(i,j)>1:continue
   R=Q(i,j);r=1/R
   for l in [Q(1,2),Q(-1,2),Q(3),Q(-3)]:
    a=l-3*r/l; b=l+3*r/l;F=(R*l*l-2*l+1)*(R*l*l+6*l+9)
    assert b*b==a*a+12*r
    assert r*r*F==((a+2*r)**2-16*r*(r-1))*l*l
    affine+=1
 return dict(ordinary_good_residue_cases=integer,rescaled_good_residue_cases=prec,rational_identities=affine)
if __name__=='__main__':print(json.dumps(run(),indent=2))
