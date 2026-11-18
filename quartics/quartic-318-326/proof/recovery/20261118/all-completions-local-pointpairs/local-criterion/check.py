"""Finite controls, not a proof of an infinite local statement."""
import json
from math import isqrt
from fractions import Fraction as F
def ls(a,p):return 0 if a%p==0 else 1 if pow(a%p,(p-1)//2,p)==1 else -1
def test():
 counts=[];boundary=[]
 for p in range(5,201):
  if any(p%d==0 for d in range(2,isqrt(p)+1)):continue
  u=next(z for z in range(2,p) if ls(z,p)<0)
  for b0 in (1,u):
   for d0 in (1,u):
    f=lambda x:b0*(1-d0*x*x)*(1+3*d0*x*x)
    atinf=1+ls(-3*b0*d0*d0,p)
    aff=sum(1+ls(f(x),p) for x in range(p));card=aff+atinf;assert card>0 and (card-p-1)**2<=4*p
    branch=any(f(x)%p==0 for x in range(p))
    if branch:assert all((4*b0*d0*x*(1-3*d0*x*x))%p for x in range(p) if f(x)%p==0)
    counts.append(card)
    if all(not(x%p and f(x)%p and ls(f(x),p)>=0) for x in range(p)):boundary.append((p,b0,d0))
 for B in [F(7),F(1,11),F(289*3),F(49)]:
  D=1-B/289;V=B*B*D
  for e,s in [(F(1),F(5)),(-F(1,3),F(19)),(F(11,7),F(3,4))]:
   E=e*B;g=e*D*(B/s)**2
   f=lambda t:(1-t)*(1+3*t)
   ysq=lambda t,x:x*(x-t)*(x+3*t)
   assert B**3*f(e)==ysq(E,B) and B**3*s**6*f(g)==ysq(E*V,B*s*s)
 return {'smooth_genus_one_residue_models':len(counts),'minimum_point_count':min(counts),'control_models_needing_boundary_lift':boundary}
if __name__=='__main__':print(json.dumps(test(),indent=2))
