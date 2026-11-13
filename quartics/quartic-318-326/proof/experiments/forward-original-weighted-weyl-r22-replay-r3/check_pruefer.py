from fractions import Fraction
from math import gcd
import json
counts=dict(dyadic_orders=0,dyadic_transitions=0,involution_detection=0,level_cardinalities=0,odd_power_maps=0,involution_injectivity=0)
for k in range(1,12):
 N=2**k
 for a in range(N):
  x=Fraction(a,N);order=N//gcd(a,N)
  assert (order*x).denominator==1
  assert x.denominator==order
  counts['dyadic_orders']+=1
  assert 2*Fraction(a,2*N)==x
  counts['dyadic_transitions']+=1
  if a:
   t=order//2;assert (t*x)%1==Fraction(1,2)
   counts['involution_detection']+=1
 for j in range(k+1):
  assert sum((2**j*a)%N==0 for a in range(N))==2**j
  counts['level_cardinalities']+=1
 for m in range(1,25,2):
  assert len({m*a%N for a in range(N)})==N
  counts['odd_power_maps']+=1
 for m in range(min(N,40)):
  injective_on_two=(m*(N//2))%N!=0
  assert injective_on_two==(len({m*a%N for a in range(N)})==N)
  counts['involution_injectivity']+=1
print(json.dumps({'status':'PASS','counts':counts},indent=2))
