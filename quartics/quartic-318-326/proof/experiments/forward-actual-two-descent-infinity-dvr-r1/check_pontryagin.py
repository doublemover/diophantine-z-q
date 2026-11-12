import json,math
from fractions import Fraction
c={'exact_dyadic_orders':0,'involution_uniqueness':0,'character_inverse':0,'precomposition_scalar':0}
for k in range(9):
 m=2**k
 for x in range(m):
  assert m//math.gcd(x,m)==(Fraction(x,m).denominator)
  c['exact_dyadic_orders']+=1
 inv=[x for x in range(m) if 2*x%m==0]
 assert len(inv)<=2
 c['involution_uniqueness']+=1
 for u in range(m):
  if math.gcd(u,m)!=1:continue
  v=pow(u,-1,m)
  for x in range(m):
   assert (v*u*x)%m==x
   c['character_inverse']+=1
   for a in [-3,0,1,6]:
    assert (u*a*x)%m==(a*(u*x))%m
    c['precomposition_scalar']+=1
print(json.dumps({'status':'PASS','scope':'Exact finite dyadic character models, inverse maps and scalar precomposition; not Lean, native topology or global duality verification','checks':c},indent=2))
