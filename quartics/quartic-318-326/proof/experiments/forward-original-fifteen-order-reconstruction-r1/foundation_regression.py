from fractions import Fraction
from math import gcd
import json
prime=lambda q:q>=2 and all(q%d for d in range(2,int(q**.5)+1))
count=0
for N in range(1,201):
 for q in range(2,N+1):
  if not prime(q) or N%q:continue
  assert N//q>0
  for n in range(1,N+1):
   if N%n:continue
   if (N//q)%n:
    assert n%q==0
    count+=1
integral=0
for p in [2,3,5,7,11,17,23,31,41]:
 for a in range(-6,7):
  for b in range(-6,7):
   for da in range(1,7):
    for db in range(1,7):
     x,y=Fraction(a,da),Fraction(b,db)
     D=x.denominator*y.denominator
     if D%p:
      assert gcd(x.denominator,p)==1 and gcd(y.denominator,p)==1
      integral+=1
# A large order may still contain a fixed prime divisor; growth is not exclusion.
assert all((3*k)%3==0 and 3*k>k for k in range(1,101))
# N=0 destroys positivity of the drop; composite q destroys prime-drop implication.
assert 0//2==0
assert 12%2==0 and 12%6==0 and (12//6)%2==0
assert 12%4==0 and 12%6==0 and (12//6)%4!=0 and 4%6!=0
# A global coordinate denominator may divide p although one local numerator cancels.
assert 39*39%49==2 and (3+39)%7==0 and (3+10)%7!=0
print(json.dumps({'prime_drop_cases':count,'denominator_integrality_cases':integral,'negative_boundary_controls':4},sort_keys=True))
