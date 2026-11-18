from fractions import Fraction as Q
from sympy import symbols,expand
x,z,k,g,b,y,c,t,R,G=symbols('x z k g b y c t R G')
for d in [-1,1]:
 for c,m in [(-d,2401*d),(-2401*d,d)]:
  h2=Q(-m,c);g2=Q(-m,c**3)
  assert h2 in (Q(2401),Q(1,2401)) and h2==c*c*g2
  ms=h2*(h2-1)/32;assert ms.numerator%2 and ms.denominator%2
h=symbols('h')
assert expand(-R**2-h**2*(1+2*R)-(h**2*(h**2-1)-(R+h**2)**2))==0
assert expand((y+R)**2+x*k*R*(y+R)+k*R**2-(y**2+(2+x*k)*R*y+(1+k+x*k)*R**2))==0
print('four sign cases, exact order-five constant and both quadratic changes verified')
