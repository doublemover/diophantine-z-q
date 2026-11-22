#!/usr/bin/env python3
"""Exact fixed first-point, isogeny, scale and secant coefficients; no delta input."""
from fractions import Fraction as Q
import json


def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out


beta=204618888056724185
t=18
A=1+3*beta*t*t
k=(1-beta*t*t)*(1-9*beta*t*t)
n=beta*k
u=beta*A*A
v=8*beta**2*t*A*(1-3*beta*t*t)
assert u>0 and v!=0 and v*v==u*(u-n)*(u+3*n)
assert u-n==(4*beta*t)**2
assert u+3*n==beta*(2*(1-3*beta*t*t))**2
a=Q(v,u)
r=u+2*n-Q(3*n*n,u)
s=v*(1+Q(3*n*n,u*u))
assert r==a*a and s==a*(u+Q(3*n*n,u))
assert s*s==r*(r*r-4*n*r+16*n*n)
factor_beta=[a*a-4*u,-2*a,1]
factor_minus3_beta=[a*a+Q(12*n*n,u),2*a,1]
discriminant=[-3*r*r+8*n*r-48*n*n,-8*s,8*n-6*r,0,1]
assert mul(factor_beta,factor_minus3_beta)==discriminant

N=n*A**2
R=r*A**2
S=s*A**3
assert all(x.denominator==1 for x in (R,S))
R,S=map(int,(R,S))
assert R==64*beta**2*t*t*(1-3*beta*t*t)**2
assert S==8*beta**2*t*(1-3*beta*t*t)*(A**4+3*k*k)
assert S*S==R*(R*R-4*N*R+16*N*N)
integer=[-3*R*R+8*N*R-48*N*N,-8*S,8*N-6*R,0,1]
assert integer==[x*A**(4-i) for i,x in enumerate(discriminant)]
print(json.dumps({
    "beta": beta, "t": t, "A": A, "n": n, "P": [u,v],
    "integer_base_parameter":N,"integer_isogeny_point":[R,S],
    "fixed_secant_polynomial_ascending":integer,
    "unexpanded_delta_or_class_evaluated":False
},indent=2))
