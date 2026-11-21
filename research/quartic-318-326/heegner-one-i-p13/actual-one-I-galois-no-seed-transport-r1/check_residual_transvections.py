#!/usr/bin/env python3
"""Finite arithmetic behind the actual mod-13 Galois / ray comparison."""
from itertools import product
import json
p=13
cnt=1+sum(sum(y*y%7==x*(x+1)*(x-3)%7 for y in range(7)) for x in range(7))
assert cnt==8 and pow((-28)%13,6,13)==12
# At 3, y²=x²(x+1) has tangents y=±x and exact Delta valuation 2.
Delta=2304
assert Delta%9==0 and Delta%27!=0 and 2%13
assert 208%3==1
# Two distinct fixed lines for order-13 unipotents supply both elementary groups.
U=(1,1,0,1); L=(1,0,1,1); I=(1,0,0,1)
def mm(a,b):
    return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%p
                 for i,j in product(range(2),repeat=2))
seen={I}; todo=[I]
for g in todo:
    for h in (U,L):
        k=mm(g,h)
        if k not in seen:seen.add(k);todo.append(k)
assert len(seen)==p*(p*p-1)==2184
det=lambda m:(m[0]*m[3]-m[1]*m[2])%p
trace=lambda m:(m[0]+m[3])%p
for t,d in product(range(p),range(1,p)):
    m=(0,-d,1,t)
    assert det(m)==d and trace(m)==t
print(json.dumps(dict(A_F7_count=cnt,Frob7_discriminant_mod13=(-28)%13,
      minimal_valuation3_Delta=2,elementary_subgroup_size=len(seen),
      full_residual_size=(p-1)*len(seen),trace_det_pairs_checked=p*(p-1)),indent=2))
