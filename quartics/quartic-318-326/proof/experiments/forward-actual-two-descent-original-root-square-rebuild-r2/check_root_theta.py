#!/usr/bin/env python3
"""Exact rational original-root formulas only; not Lean or divisor/Weil/global duality."""
from fractions import Fraction as F
from itertools import product
import json
count=dict(curve_translation=0,weight_table=0,commutator=0,square_multipliers=0,translation_composition=0)
for n in map(F,[-7,-3,-1,1,2,5,9]):
 roots=[0,n,-3*n]
 def poly(x):return x*(x-n)*(x+3*n)
 def tx(x,i):return [-3*n*n/x,n*(x+3*n)/(x-n),-3*n*(x-n)/(x+3*n)][i]
 def sy(x,i):return [3*n*n/x**2,-4*n*n/(x-n)**2,-12*n*n/(x+3*n)**2][i]
 def w(x,i):return x-roots[i]
 for a,b in product(range(-15,16),[1,2,3,5]):
  x=F(a,b)
  if x in roots:continue
  numer=[[-3*n*n,-n*(x+3*n),3*n*(x-n)],[n*(x+3*n),4*n*n,4*n*x],[-3*n*(x-n),-4*n*x,12*n*n]]
  for i in range(3):
   assert tx(x,i) not in roots
   assert sy(x,i)**2*poly(x)==poly(tx(x,i))
   count['curve_translation']+=1
   assert w(x,i)*w(tx(x,i),i)==[-3*n*n,4*n*n,12*n*n][i]
   count['square_multipliers']+=1
   for j in range(3):
    assert w(tx(x,i),j)==numer[i][j]/w(x,i)
    count['weight_table']+=1
    ratio=w(x,i)*w(tx(x,i),j)/(w(x,j)*w(tx(x,j),i))
    assert ratio==(1 if i==j else -1)
    count['commutator']+=1
    assert tx(tx(x,i),j)==tx(tx(x,j),i)
    assert sy(x,i)*sy(tx(x,i),j)==sy(x,j)*sy(tx(x,j),i)
    count['translation_composition']+=1
print(json.dumps({'status':'PASS','scope':__doc__,'checks':count},indent=2))
