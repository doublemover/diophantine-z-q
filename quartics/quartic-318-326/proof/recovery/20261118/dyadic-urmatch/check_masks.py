from fractions import Fraction as F
from itertools import product
from sympy import symbols,expand
q,K,D=symbols('q K D');P=q-1;z=1+2*P
assert expand(z*((1-D)/2+P)+((1-K)/2+P)*P**2-(q**3-(1+K)*q**2/2+(K-D)*q-(K-D)/2))==0
for ep,m,d,a in product((0,1),range(3),(-1,1),(-1,1)):
 e=[(2**ep)*x for x in (0,8,19208)];j,k=[x for x in range(3) if x!=m]
 H=F(d*(e[j]-e[k]),4);D=e[j]-e[m]
 assert (H/2**((1 if j==0 else 6)+ep)).numerator%2 and F(D,2**(3+ep)).numerator%2
 if j==0:
  Ns=[F(e[k],8*2**ep),F(e[m],8*2**ep)]
  assert set(Ns)=={1,2401}
print('all 24 signed/index/scaling cases and exact central cubic coefficient checked')
