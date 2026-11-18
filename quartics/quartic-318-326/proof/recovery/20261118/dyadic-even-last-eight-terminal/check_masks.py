from fractions import Fraction as F
from itertools import product
from collections import Counter
from sympy import symbols,expand
f,P,V,w,g=symbols('f P V w g')
B=g+w*(P+V)
assert expand(f*B**2+w*w*P*B+(w*P)**2-(f*g*g+w*w*(f*(P+V)**2+P*(g+w*(P+V))+P**2))-2*f*g*w*(P+V))==0
mods=Counter()
for C,d,a in product((-343,375),(-1,1),(-1,1)):
 f0=a*(32-C);m0=-d;t=F(m0,f0**5);k=t.numerator*pow(t.denominator,-1,4)%4; assert k in (1,3)
 mods[k]+=1
assert mods=={1:4,3:4}
print('eight representatives; both unit-residue regimes 4+4 and exact divided base identity verified')
