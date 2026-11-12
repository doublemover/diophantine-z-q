from fractions import Fraction as Q
from itertools import product
import json
counts=dict(reciprocal_polynomial_square=0,all_place_coordinate_branches=0,full_dual_counit=0,full_dual_action=0,negative_controls=0)
def vp(x,p):
 if x==0:return 999
 def nval(n):
  n=abs(n);v=0
  while n%p==0:n//=p;v+=1
  return v
 return nval(x.numerator)-nval(x.denominator)
for a in range(-12,13):
 for b in range(1,13):
  t=Q(a,b)
  for p in [2,3,5,7]:
   assert vp(t,p)>=0 or vp(1/t,p)>=0
   counts['all_place_coordinate_branches']+=1
  if not t:continue
  s=1/t
  for cs in product(range(-1,2),repeat=3):
   lhs=sum(Q(c)*s**i for i,c in enumerate(cs));rhs=sum(Q(c)*t**(-i) for i,c in enumerate(cs))
   assert lhs==rhs;counts['reciprocal_polynomial_square']+=1
# Entire dual on a rank-two nonreduced finite algebra, not just one frame functional.
for p in [2,3,5]:
 A=list(product(range(p),repeat=2));one=(1,0)
 def mul(a,b):return(a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)
 for g in A:
  def value(x):return(g[0]*x[0]+g[1]*x[1])%p
  def coinduce(m,a):return value(mul(a,m))
  for m in A:
   assert coinduce(m,one)==value(m);counts['full_dual_counit']+=1
   for a in A:
    for b in A:
     assert coinduce(mul(a,m),b)==coinduce(m,mul(a,b));counts['full_dual_action']+=1
assert Q(2)!=1/Q(2);counts['negative_controls']+=1
assert vp(Q(1,2),2)<0;counts['negative_controls']+=1
assert vp(Q(2),2)>=0 and vp(Q(1,2),2)<0;counts['negative_controls']+=1
# Scalar action is multiplication precomposition, not pointwise coefficient multiplication.
a=(0,1);m=(1,0);b=(1,0);g=(0,1)
assert (g[0]*mul(a,m)[0]+g[1]*mul(a,m)[1])%5 != a[0]*((g[0]*m[0]+g[1]*m[1])%5)%5
counts['negative_controls']+=1
print(json.dumps({'status':'PASS','checks':counts,'scope':'Independent finite rational/finite-ring identities only; not integrality, normalization, global duality, or Lean kernel verification.'},indent=2))
