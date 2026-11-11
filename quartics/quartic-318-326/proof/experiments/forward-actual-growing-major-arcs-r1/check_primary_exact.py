from fractions import Fraction
from math import gcd
import json
c=dict(directed_scalar_squares=0,dyadic_halves=0,all_integer_roots=0,finite_annihilator_checks=0)
for i in range(9):
 for j in range(i,10):
  for a in range(-20,21):
   assert Fraction(a,2**i)==Fraction(2**(j-i)*a,2**j)
   c['directed_scalar_squares']+=1
for k in range(10):
 for a in range(2**k):
  x=Fraction(a,2**k)
  assert 2*Fraction(a,2**(k+1))==x;c['dyadic_halves']+=1
  for m in range(1,20):
   v=0;b=m
   while b%2==0:v+=1;b//=2
   N=2**(k+v);u=pow(b,-1,N) if N>1 else 0
   y=Fraction(a*u,N)
   assert (m*y-x).denominator==1;c['all_integer_roots']+=1
for N in range(1,65):
 for m in range(1,65):
  surj=gcd(m,N)==1
  kills=all(m*x%N==0 for x in range(N))
  if surj and kills:assert N==1
  c['finite_annihilator_checks']+=1
print(json.dumps({'status':'PASS','counts':c},indent=2))
