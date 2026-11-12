from fractions import Fraction as F
from itertools import product
from math import prod
import json
n=0
for nt in range(-15,16):
 t=F(nt,3)
 a=list(map(F,[-2,-1,1,3]))
 if not t or t in a:continue
 for y in product([F(-2),F(-1),F(1),F(3)],repeat=4):
  d=[y[i]**2/(t-a[i]) for i in range(4)]
  s=1/t;v=[r*s for r in y]
  assert all(v[i]**2==d[i]*s*(1-a[i]*s) for i in range(4))
  df=16*prod(y);di=16*prod(v)
  assert di==s**4*df
  z=F(5,7);zs=-t*t*z
  assert di*zs==-s*s*df*z
  assert all(t*v[i]==y[i] for i in range(4))
  n+=1
assert F(2)**4!=F(2)**2
assert -F(3)**2*F(5,7)!=F(3)**2*F(5,7)
print(json.dumps({'status':'PASS','signed_root_and_different_cases':n,'negative_controls':2,
 'scope':'Exact rational signed root, radicand, different and differential coefficient identities; not integral-closure/Hom equivalence or Lean kernel verification.'},indent=2))
