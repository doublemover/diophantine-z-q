from fractions import Fraction as F
from itertools import product
from math import isqrt
from pathlib import Path
import json

def square(v):
 if v<0:return False
 a,b=isqrt(v.numerator),isqrt(v.denominator)
 return a*a==v.numerator and b*b==v.denominator

def add(n,P,Q):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 if x==z and y==-w:return None
 m=(3*x*x+4*n*x-3*n*n)/(2*y) if x==z else (y-w)/(x-z)
 u=m*m-2*n-x-z;v=m*(x-u)-y
 assert v*v==u*(u-n)*(u+3*n)
 return u,v

def coord(n,r,P):
 if P is None:return F(1)
 x,y=P
 return F(3*r*r+4*n*r-3*n*n) if x==r else x-r

families=points=pair_checks=nonexception=0
for beta in [17,41,73,97,137,193,241,313,401,577]:
 for t in range(1,isqrt((beta-1)//9)+1):
  den=beta+3*t*t;n=beta*(beta-t*t)*(beta-9*t*t)
  if square(F(beta,n)):continue
  x=F(beta*den*den);u=F(2*(beta-3*t*t));v=F(4*beta*t);y=F(beta*den)*u*v
  assert x+3*n==beta*u*u and x-n==v*v and y*y==x*(x-n)*(x+3*n)
  P=(x,y);T1=(F(n),F(0));T2=(F(-3*n),F(0));values=[]
  for eps,c,e in product(range(2),repeat=3):
   R=P if e else None
   if eps:R=add(n,R,T2)
   if c:R=add(n,R,T1)
   A=coord(n,-3*n,R);B=coord(n,n,R);ca=F(3**eps*n**c*beta**e);cb=F((-n)**eps)
   assert A and B and square(A/ca) and square(B/cb)
   values.append((A,B));points+=1
   if e:
    assert R is not None and all([R[0],R[0]-n,R[0]+3*n]);nonexception+=1
  for i in range(8):
   for j in range(8):
    equal=square(values[i][0]/values[j][0]) and square(values[i][1]/values[j][1])
    assert equal==(i==j);pair_checks+=1
  families+=1
cube=list(product(range(2),repeat=3));inj=0
for coeffs in product(range(2),repeat=9):
 images=[tuple(sum(coeffs[3*i+j]*v[j] for j in range(3))%2 for i in range(3)) for v in cube]
 if len(set(images))==8:
  assert set(images)==set(cube) and (0,0,1) in images;inj+=1
subgroups=0
for mask in range(256):
 S={cube[i] for i in range(8) if mask>>i&1}
 plane={(e,c,0) for e,c in product(range(2),repeat=2)}
 if not plane<=S:continue
 if all(tuple(a[j]^b[j] for j in range(3)) in S for a in S for b in S):
  assert len(S) in [4,8];assert ((0,0,1) in S)==(len(S)==8);subgroups+=1
result={'status':'PASS','actual_rational_twist_families':families,'actual_generated_cube_points':points,'actual_squareclass_pair_comparisons':pair_checks,'nonexceptional_beta_coset_points':nonexception,'binary_cube_linear_maps':512,'bijective_maps':inj,'subgroups_containing_torsion_plane':subgroups,'scope':'Actual eight generated Kummer cosets and finite-cardinality logic; no exhaustive rational group count or global quotient-cardinality premise is inferred.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
