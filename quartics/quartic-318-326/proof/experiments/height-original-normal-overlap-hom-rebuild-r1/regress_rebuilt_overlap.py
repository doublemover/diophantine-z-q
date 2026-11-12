from fractions import Fraction as F
from itertools import product
import json
count=0;wrong=False;miss=False
for x in [F(-3),F(-2),F(-1),F(1,2),F(2),F(3)]:
 for c in product(range(-2,3),repeat=4):
  exps=[-2,-1,0,1]
  z=sum(F(a)*x**k for a,k in zip(c,exps))
  inv=sum(F(a)*(1/x)**k for a,k in zip(c,exps))
  assert sum(F(a)*(1/(1/x))**k for a,k in zip(c,exps))==z
  assert x**2*z==sum(F(a)*x**(k+2) for a,k in zip(c,exps))
  wrong |= inv != z
  miss |= z != sum(F(a)*x**(k+2) for a,k in zip(c,exps))
  count+=1
assert wrong and miss
print(json.dumps({'status':'PASS','exact_laurent_cases':count,'negative_controls':2,'scope':'Finite rational controls for inversion and power clearing, not general integral closure or Lean acceptance.'}))
