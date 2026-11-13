from itertools import product
from math import gcd,lcm
import json
values=[0,1,2,3,6]
patterns=list(product([False,True],repeat=3))
flip=lambda t:tuple(not x for x in t)
left=lambda a,b,t:tuple(b[i] if t[i] else a[i] for i in range(len(t)))
right=lambda a,b,t:tuple(a[i] if t[i] else b[i] for i in range(len(t)))
checked=obstructed=surviving=0
for a in product(values,repeat=3):
 for b in product(values,repeat=3):
  good=[s for s in patterns if gcd(lcm(*left(a,b,s)),lcm(*right(a,b,s)))==1]
  for q in [2,3]:
   for t in patterns:
    if not all(n%q==0 for n in left(a,b,t)):continue
    assert all(s==t or s==flip(t) for s in good)
    assert len(good)<=2
    assert bool(good)==(t in good or flip(t) in good)
    checked+=1;obstructed+=not bool(good);surviving+=bool(good)
# Counterexample to coverage implying either candidate succeeds.
a,b=(6,10),(5,3);t=(False,False)
assert all(n%2==0 for n in left(a,b,t))
assert gcd(lcm(*left(a,b,t)),lcm(*right(a,b,t)))==15
assert gcd(lcm(*left(a,b,flip(t))),lcm(*right(a,b,flip(t))))==15
# Exact15-index coverage and repeated source positions retained.
large=0
for k in range(50):
 t=tuple(bool((i+k)%2) for i in range(15))
 a=tuple(3 if t[i] else 2 for i in range(15));b=tuple(2 if t[i] else 3 for i in range(15))
 good=[]
 for s in product([False,True],repeat=15):
  if gcd(lcm(*left(a,b,s)),lcm(*right(a,b,s)))==1:good.append(s)
 assert set(good)=={t,flip(t)}
 large+=1
print(json.dumps({'exhaustive_known_divisor_orientations':checked,'empty_candidate_controls':obstructed,'nonempty_candidates':surviving,'full_fifteen_enumerations':large,'coverage_without_success_counterexample':True},sort_keys=True))
