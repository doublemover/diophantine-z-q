"""Exact recovery of both rational parameters from the known 409 specialization."""
from fractions import Fraction as F
from math import isqrt
import json
def sqrt(x):
    p,q=isqrt(x.numerator),isqrt(x.denominator)
    assert F(p*p,q*q)==x
    return F(p,q)
def e(t):return (1-17*t*t)*(1-153*t*t)/(1+51*t*t)**2
u=F(204,1073); B=17*u*u; D=1-B/289; V=B*B*D
E=F(2014880256,4864365025); S=F(-1424848608,2768946245)
def recover(n,U):
    x=17*U*U
    a=sqrt(x-n)/(17*U); b=sqrt((x+3*n)/17)/U
    assert b*b+51*a*a==4
    t=a/(2+b)
    assert e(t)==n/x and b==2*(1-51*t*t)/(1+51*t*t)
    return t
t=recover(E,u);v=recover(E*V,u*S)
z=sqrt(e(v)/(409*e(t)))
out=[dict(beta=17,theta=409,t=str(t),v=str(v),et=str(e(t)),ev=str(e(v)),quotient_square_root=str(z))]
beta,theta,N=17,409,17*409
def step(P,Q):
    x,y=P; x1,y1=Q
    m=(3*x*x-164*N*x+81*N*N)/(2*y) if P==Q else (y1-y)/(x1-x)
    X=m*m+82*N-x-x1;Y=m*(x-X)-y
    assert Y*Y==X*(X-N)*(X-81*N)
    return X,Y
def proj(t):
    Z=sqrt(theta*(9-beta*t*t)*(1-9*beta*t*t))
    X=9*beta*beta*theta*t*t
    Y=9*beta*beta*theta*t*Z
    assert Y*Y==X*(X-N)*(X-81*N)
    return X,Y
P=proj(t);P3=step(P,step(P,P));t3=sqrt(P3[0]/(9*beta*beta*theta));v3=-1/(beta*t3)
assert abs(proj(t3)[1])==abs(P3[1]);z3=sqrt(e(v3)/(theta*e(t3)))
out.append(dict(XP=str(P[0]),YP=str(P[1]),t3=str(t3),v3=str(v3),quotient_square_root3=str(z3)))
print(json.dumps(out,indent=2))
