from fractions import Fraction as F
from math import gcd
from itertools import product
import json
def cubic(X,n):return X*(X-n)*(X+3*n)
def chi(x,p):return pow(x%p,(p-1)//2,p)
identities=0
for th in [1,17,41,409,457]:
 for h in range(1,9):
  q=F(th*h*h, 317**2)
  a=3*(3+q)*(1-q);n=(2+q)*(3+q)*(1-q)
  assert cubic(a,n)==(a*a/3)**2
  assert cubic(a,n*q)==((1+q)*a*a/3)**2
  assert F(3*(3*317**2+th*h*h)*(317**2-th*h*h),317**4)==a
  identities+=1
psi=lambda z:3*z**4+8*z**3-18*z*z-9
assert all(psi(z)%5 for z in range(5))
print(json.dumps(dict(exact_rational_point_triples=identities,division_polynomial_finite_residues_mod5=[psi(z)%5 for z in range(5)],division_polynomial_infinity_mod5=3),indent=2))
