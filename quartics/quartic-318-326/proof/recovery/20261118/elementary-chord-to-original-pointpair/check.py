"""Check the chord search and its exact inverse by rational arithmetic, including boundary cases."""
from fractions import Fraction as Q
from itertools import combinations
import json
def gain(B,t):
 if t is None:return Q(1),Q(0)
 e=(t*t-B)/(t*t+3*B)
 return e,t*(1-e)
def check():
 count=torsion=0
 for beta in (Q(17),Q(41),Q(187)):
  pts={gain(beta,Q(t,j)) for t in range(-11,12) for j in range(1,6)}|{gain(beta,None)}
  for (e,Y),(f,Z) in combinations(sorted(pts),2):
   if e==f or e*f<=0: continue
   theta=e*f;m=(Y-Z)/(e-f);c=(Y-m*e)/beta;k=-2*m/beta
   A=12+beta*k*k;C=4+2*beta*c*k;u=A/2;s=A*(e-f)/4
   assert theta*u*u==(beta*c*c-1)*A and s*s==16+beta*(k-2*c)*(k+6*c)
   assert (C+2*s)/A==e and (C-2*s)/A==f
   assert Y==beta*c-beta*k*e/2 and Z==beta*c-beta*k*f/2
   count+=1;torsion+=int(Y==0 or Z==0)
 return dict(exact_chord_roundtrips=count,including_zero_ordinate=torsion)
if __name__=='__main__':print(json.dumps(check(),indent=2))
