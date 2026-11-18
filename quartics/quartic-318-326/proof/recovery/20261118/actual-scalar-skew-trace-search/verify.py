"""Exact search floor for the negative translated isogeny parameter of the *indexed* scalar. Not a global obstruction."""
from fractions import Fraction as F
from math import prod
r=4376874610839020; A=114444*r; beta=204618888056724185
primes=[5,11,17,163,661,733,1489,1861];assert prod(primes)==beta
# W = N² + r Q²; |H| in (0.01,1], 0<=J<=1, |fixedNorm|<1.
Wup=(1+F(1,r*r)+F(2,r))**2 + F(10_000,r**29)
Rup = F(A,17*(1+A)**2)*Wup**2
e=F(125131411,10**19) # 1.25131411e-11
assert e-Rup/6>0 and (e-Rup/6)**2>4*Rup/3
bound=90_422_000_000_000
assert e*(2+e)*bound**2 < beta
# Original D=6 mod7 (from indexed sign proof); 16-3R=13+3D
assert (13+3*6)%7==3 and pow(3,3,7)==6
print('certified denominator greater than',bound)
