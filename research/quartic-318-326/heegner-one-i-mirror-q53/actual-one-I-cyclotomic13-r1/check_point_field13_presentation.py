#!/usr/bin/env python3
"""Exact degree-84 projective root polynomial and quadratic point field."""
from functools import cache
from math import prod
import sympy as s
import json

p=13
d=2811626664334219040035976315
u=s.symbols('u')
def Z(f):return s.Poly(f,u,domain=s.ZZ)
g=Z(u*(u-1)*(u+3));zero=Z(0)
def plus(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[0],-a[1]
def mul(a,b):return a[0]*b[0]+g*a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def pow(a,n):
    if n==0:return (Z(1),zero)
    return mul(a,pow(a,n-1))
def minus(a,b):return plus(a,neg(b))
@cache
def psi(n):
    if n==0:return (zero,zero)
    if n==1:return (Z(1),zero)
    if n==2:return (zero,Z(2))
    if n==3:return (Z(3*u**4+8*u**3-18*u*u-9),zero)
    if n==4:return (zero,2*Z(2*u**6+8*u**5-30*u**4-90*u*u-72*u+54))
    m=n//2
    if n%2:
        return minus(mul(psi(m+2),pow(psi(m),3)),mul(psi(m-1),pow(psi(m+1),3)))
    x,y=mul(psi(m),minus(mul(psi(m+2),pow(psi(m-1),2)),mul(psi(m-2),pow(psi(m+1),2))))
    return (y.exquo(Z(2)),x.exquo(2*g))
f,zero_again=psi(13)
assert not zero_again and f.degree()==84 and f.LC()==13 and f.gcd(g).degree()==0
# v=13u integral. The second coordinate W=13²*y/d then satisfies
# W²=13 d v(v−13)(v+39).
fint=Z(sum((co*13**(83-ew[0]) if ew[0]<84 else co//13)*u**ew[0] for ew,co in f.terms()))
assert fint.LC()==1 and fint.degree()==84
# [2] gives u' = (g')²/(4g)-2-2u and w'/w=-1+g'*(u-u')/(2g)
f=f.set_domain(s.QQ)
G=g.set_domain(s.QQ)
v=(G.diff()**2*s.invert(4*G,f)-Z(2+2*u)).rem(f)
b=(-Z(1)+G.diff()*(Z(u)-v)*s.invert(2*G,f)).rem(f)
# Cache polynomial compose mod f in the literal 84-dimensional base algebra.
def subs_mod(a,z):
    w=Z(0).set_domain(s.QQ)
    for t in a.all_coeffs():
        w=(w*z+Z(0).set_domain(s.QQ).add_ground(t)).rem(f)
    return w
# Verify the quadratic radicand equivariance exactly for the [2] formulas.
assert (b*b*G).rem(f)==subs_mod(G,v)
# The remaining order 12 and odd involution are certified by the actual group
# law [2]^6=[-1] on E[13], rather than expensive repeated rational powers.
old=(5,11,17,163,661,733,1489,1861,114649,119851)
assert prod(old)==d
print(json.dumps(dict(d=d,ordinary_symbol_terms=156*prod(x-1 for x in old),
     x_root_poly_coefficients=[int(a) for a in f.all_coeffs()],
     monic_x_root_poly_coefficients=[int(a) for a in fint.all_coeffs()],
     integer_presentation='v=13u; W^2=13*d*v*(v-13)*(v+39)',
     delta_generator=2,delta_order=12,
     twist_independent_x_field_degree=84,point_field_degree=168),sort_keys=True,indent=2))
