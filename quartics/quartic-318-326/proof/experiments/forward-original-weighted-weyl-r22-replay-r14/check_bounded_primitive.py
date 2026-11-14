from fractions import Fraction as F
from math import gcd,isqrt,ceil
from collections import defaultdict
import json
C=dict(coordinate_box_shrink=0,actual_bounded_ray_cover=0,actual_primitive_box_mass=0,canonical_linear_mass=0,positive_normalization_lower=0,quadratic_primitive_lower=0,negative_controls=0)
for H in range(16):
 for d in range(1,12):
  for z in range(-20,21):
   if abs(d*z)<=H:assert abs(z)<=H;C['coordinate_box_shrink']+=1
for k in [2,318,326]:
 for H in [8,16,24]:
  left=defaultdict(list)
  for a in range(1,H+1):
   for b in range(-H,H+1):left[a*a+b*b].append((a,b))
  points=set()
  for c in range(1,H+1):
   for d in range(-H,H+1):
    for w in range(1,isqrt(2*H*H//k)+1):
     for a,b in left[c*c+d*d+k*w*w]:points.add((a,b,c,d,w))
  primitive={v for v in points if gcd(*v)==1}
  for v in points:
   d=gcd(*v);u=tuple(x//d for x in v)
   assert d>=1 and u in primitive and max(map(abs,u))<=H and d<=H
   C['actual_bounded_ray_cover']+=1
  assert len(points)<=len(primitive)*(H+1)
  # Original nonconstant weight stays on v, not u.
  weights=[F(1,1+sum(abs(x) for x in v)) for v in points]
  assert sum(weights)<=len(primitive)*(H+1)
  C['actual_primitive_box_mass']+=1
for R in [F(1),F(3,2),F(7,3)]:
 for B in [F(1),F(3,2),F(7),F(21,2)]:
  H=ceil(R*B)
  for M in [F(0),F(1,3),F(5)]:
   A=(R+2)*(M+1)
   assert A>0 and (H+1)*M<=A*B
   C['canonical_linear_mass']+=1
for S in [F(1,3),F(2),F(11)]:
 for A in [F(1,2),F(3),F(7)]:
  for B in [F(1),F(3,2),F(7),F(21)]:
   P=ceil(S*B*B/(2*A));Z=S*B**3/2
   assert Z/B**3==S/2 and Z<=P*A*B
   C['positive_normalization_lower']+=1
   c=S/(2*A);assert c*B*B<=P
   C['quadratic_primitive_lower']+=1
assert abs(F(1,2)*10)<=5 and abs(10)>5;C['negative_controls']+=1 # integer-positive required
assert not (F(1,2)>0 and F(1,2)>=1);C['negative_controls']+=1
assert F(2)**3/F(2)==F(2)**2 and F(2)**3/F(2)!=F(2)**3;C['negative_controls']+=1
assert F(1,1+2)!=F(1,1+1);C['negative_controls']+=1
print(json.dumps({'status':'PASS','checks':C,'scope':'Exact bounded original integer rays, true primitive carrier, original weight mass and rational lower-bound normalization. Not numerical infinite-limit verification or prime values.'},indent=2))
