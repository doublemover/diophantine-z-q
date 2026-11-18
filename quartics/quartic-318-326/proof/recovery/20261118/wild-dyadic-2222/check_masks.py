from fractions import Fraction as F
from sympy import symbols,expand
from itertools import product
b=(0,32,76832); assert [F(375*j,343+j) for j in b]==[0,32,F(1120,3)]
K=F(35,3); L=2*K-1; assert K-1==F(32,3) and L==F(67,3)
for d,a in product((1,-1),repeat=2):
 m=int(d==1)
 assert (a*(d-375)-2*m*m)%4==0
 f0=-375*a; c=(L-F(d,f0**3))/2
 assert c.denominator%2 and int(c.numerator%2)==(a*d==-1)
 if a*d==1: assert (c/2).numerator%2==0
k,j,g=symbols('k j g')
assert expand((j-k+1)*(j-k+1+2*k-1+g)+k*(k-1)-(j**2+(1+g)*j-(k-1)*g))==0
print('Mobius contacts/ratios, transformed product and four parities: OK')
