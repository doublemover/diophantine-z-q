from fractions import Fraction as F
from sympy import symbols,expand
from itertools import product
b=[0,32,76832];D,L,i,S,B,J=symbols('D L i S B J')
# Cleared change-of-variable identity modulo L^2-i^2=4DJ.
Y=2*D*B+(L-i)*S
assert expand(Y**2+2*i*S*Y-4*D*(D*B**2+L*S*B+J*S**2)-(L**2-i**2-4*D*J)*S**2)==0
for d in (-1,1):
 for j,k,m in [(0,1,2),(0,2,1),(1,2,0)]:
  H=d*(b[j]-b[k])//4;M=d*(b[m]-b[j])//2
  assert M%16==0 and(M//16)%2
  if j==0:
   K=-F(M//16,H//8);assert K in (F(2401),F(1,2401))
   assert ((K-1)/32).numerator%2 and ((K-1)/32).denominator%2
  else:assert H//256==-75*d and M//16==-d
print('six signs; integral variable change, exact unit ratios and order-five constant verified')
