from math import gcd,lcm
from itertools import product
import json
mod=lambda a,b,n: a==b if n==0 else a%n==b%n
checks=zero=0
for A,B,L,h0 in product(range(9),repeat=4):
 if gcd(A,B)!=1 or gcd(B,L)!=1:continue
 g=gcd(A,L);pred=(h0==0 if g==0 else h0%g==0)
 upper=max(h0,1)+max(1,A)*max(1,B)*max(1,L)
 found=any(mod(h,0,A) and mod(h,1,B) and mod(h,h0,L) for h in range(upper+1))
 assert pred==found
 checks+=1;zero+=int(A==0 or B==0 or L==0)
# Exact15-index LCM tests are synthetic arithmetic, not computed elliptic orders.
entries=0
for t in range(1,31):
 xs=[1+(i*i+3*t)%16 for i in range(15)]
 N=lcm(*xs)
 for M in range(0,100):
  assert (M%N==0)==all(M%n==0 for n in xs)
  entries+=1
cross=0
for q in [2,3,5,7,11]:
 for t in range(1,31):
  xs=[1+(i+t)%17 for i in range(15)];ys=[1+(3*i+t)%19 for i in range(15)]
  xs[t%15]*=q;ys[(t*7)%15]*=q
  assert gcd(lcm(*xs),lcm(*ys))%q==0
  cross+=1
# Exact continuity may hold without historical gcd16 or Pi-coprime-L.
assert gcd(4,8)==4 and mod(16,0,4) and mod(16,1,3) and mod(16,8,8)
# Shared divisor at both sides obstructs; growth alone does not remove a fixed divisor.
assert gcd(6,10)>1 and all((3*n)%3==0 for n in range(1,100))
# Primary annihilator0 is automatic and cannot imply a fixed nonzero denominator support.
assert all(0%n==0 for n in [2,3,5,7])
print(json.dumps({'exact_CRT_cases':checks,'zero_modulus_cases':zero,'synthetic_fifteen_LCM_cases':entries,'synthetic_cross_obstructions':cross,'boundary_controls':4},sort_keys=True))
