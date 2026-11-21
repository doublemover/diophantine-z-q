"""Exact changed-line toy point and elliptic target checks."""
from fractions import Fraction as Q
from math import isqrt
import json
def root(z):
    a,b=isqrt(z.numerator),isqrt(z.denominator)
    assert a*a==z.numerator and b*b==z.denominator
    return Q(a,b)
b,theta=17,1033
c,t,T=Q(21,6043),Q(75,1139),Q(27,391)
u=b*c*c
d=1-u
G=lambda v:1-b*v*v
H=lambda v:1-9*b*v*v
P=lambda v:b*G(v)*H(v)
assert (t+c)/(1+b*c*t)==T
assert root(d/theta)==Q(188,6043)
assert G(T)==G(t)*d/(1+b*c*t)**2
W=root(H(t)*((1+b*c*t)**2-9*b*(t+c)**2))
assert root(H(t)/646)==Q(26,1139)
assert root(H(T)/646)==Q(8,391)
assert root(P(t)/323)==Q(9776,76313)
assert root(P(T)/333659)==Q(32,8993)
def point(v):
    a=1+3*b*v*v; f=4*b*v; z=2*(1-3*b*v*v)
    X,Y=b*a*a,b*a*f*z
    D=P(v)
    assert X-D==f*f and X+3*D==b*z*z
    assert X*(X-D)*(X+3*D)==Y*Y and Y
    return X,Y
assert all(point(z) for z in (t,T))

a,b,c1,e,f=(-9*u**3+81*u**2,144*u**2,82*u**2-18*u,-16*u,1-9*u)
I=12*a*f-3*b*e+c1*c1
J=72*a*c1*f+9*b*c1*e-27*a*e*e-27*b*b*f-2*c1**3
r,s=16*u*u,u*(25*u-9)
A=-r-s; B=r*s
c4=16*(A*A-3*B);c6=-64*A**3+288*A*B
assert c4==I and 2*c6==J
Bp=(r-s)**2; Ap=-2*A
X4=9*u*d; Y4=8*u*X4
assert Y4**2==X4*(X4**2+Ap*X4+Bp)
assert X4**2==Bp
m=(3*X4**2+2*Ap*X4+Bp)/(2*Y4)
assert m*m-Ap-2*X4==0 and m*X4-Y4==0
assert root(X4/(17*theta))==3*Q(21,6043)*Q(188,6043)
print(json.dumps(dict(scope="changed-line exact arithmetic control, not an original linked pole",
                      beta=17,theta=theta,c_prime="21/6043",delta_prime=str(d),
                      t=str(t),t_prime=str(T),W=str(W),exact_twists=[323,333659],
                      common_H_class=646,J_roots=list(map(str,[0,r,s])),
                      target_order_four=[str(X4),str(Y4)]),indent=2,sort_keys=True))
