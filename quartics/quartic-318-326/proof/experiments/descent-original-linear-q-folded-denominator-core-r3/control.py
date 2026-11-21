from fractions import Fraction as Q
from itertools import product
from math import isqrt
ps=[3,5,7,11,13,17,19,23]; n=0
def v(p,x):
 e=0
 for a,k in [(abs(x.numerator),1),(x.denominator,-1)]:
  while a%p==0:
   a//=p;e+=k
 return e
for q in ps[:4]:
 for ns in [(5,7,11,13,17),(3,3,5,5,13),(11,17,19,19,23)]:
  N=q
  for a in ns:N*=a
  for num,den in product(range(1,40),repeat=2):
   s=Q(num,den)
   if all(v(p,s)>=0 for p in {q,*ns}):
    b=N*s**2
    assert isqrt(b.denominator)**2==b.denominator
    n+=1
print(f"PASS {n} exact lowest-term six-place controls, including repeated contacts")
