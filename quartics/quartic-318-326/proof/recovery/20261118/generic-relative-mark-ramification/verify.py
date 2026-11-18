from fractions import Fraction as F
from math import gcd,isqrt
import json
ct=0
for b in (2,5,17,187):
 for s in range(-10,11):
  for v in range(-10,11):
   if not v or (3*b-v*v+2*v*s)==0:continue
   t=F((3*b-v*v)*s-6*b*v,3*b-v*v+2*v*s)
   if s==t or s*t==b:continue
   y=s*t+3*b+v*(s-t)
   assert y*y==(s*s+3*b)*(t*t+3*b)
   R=(s-t)/(s*t-b)
   assert R==F(2*v*(s*s+3*b),(3*b-v*v)*(s*s-b)-8*b*v*s)
   assert (1-b*R*R)*(s*t-b)**2==(s*s-b)*(t*t-b)
   ct+=1
d=4376874610839020;b=204618888056724185
assert d%17==5 and 187*d==4*b and 3*187==561
sq=sorted({i*i%17 for i in range(1,17)});assert 3 not in sq and 5 not in sq
print(json.dumps(dict(rational_fiber_checks=ct,source_control=dict(d=d,beta=b),nonzero_squares_mod17=sq,formal_coefficient=187,candidate_constant=561),indent=2))
