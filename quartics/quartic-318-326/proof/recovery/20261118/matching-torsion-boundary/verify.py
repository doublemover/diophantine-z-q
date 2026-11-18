from fractions import Fraction as F
from math import isqrt
import json
def sqrt(x):
 a,b=isqrt(x.numerator),isqrt(x.denominator)
 assert F(a*a,b*b)==x
 return F(a,b)
b,th,N=17,409,6953
x=F(118201,81);y=F(1547014688,729)
assert y*y==x*(x-N)*(x-81*N)
u1=(y/x)**2; xtrans=F(-100*N)+3600*N*N/(u1+100*N)
X=(xtrans+100*N)/4;u=sqrt(X/(9*b*b*th)); k=1/(b*u);m=b*k*k;C=th*(1-m)
r=b*C*(25*m-9);s=16*b*C*m
assert sqrt((1-b*u*u)/th) and sqrt(25-9*b*u*u)
assert sqrt(-C/b) and sqrt(b*(25*m-9)) and sqrt(r*s) and sqrt(-r/b)
print(json.dumps(dict(x=str(x),isogeny_x=str(u1),translated_x=str(xtrans),X=str(X),u=str(u),k=str(k),class_minusC_over_beta_sqrt=str(sqrt(-C/b)),class_beta_times_25m_minus9_sqrt=str(sqrt(b*(25*m-9)))),indent=2))
