#!/usr/bin/env python3
from fractions import Fraction as Q
from collections import Counter
import json

n=323
x,y=Q(9226753553,5973136),Q(1005467646233175,14598344384)
r,u,v=Q(23297,2444),Q(29719,2444),Q(85425,2444)
c,e=Q(204,613),Q(611,613)
b=c*c;B=17*b;s=B*e;lam=c/r;T=n*lam**2
y1,y2=y*lam**3,y*(lam*s)**3
assert min(x,y,r,u,v,c,e,b,s,lam,T,y1,y2)>0 and b<17
assert x==17*r*r and x+3*n==17*u*u and x-n==v*v and y==17*r*u*v
def cubic(x,n):return x*(x-n)*(x+3*n)
assert y*y==cubic(x,n)
assert 1-b/17==e*e and B*B*(1-b/17)==s*s and b.denominator==613**2
assert y1*y1==cubic(B,T) and y2*y2==cubic(B*s*s,T*s*s)
e0,s0,p0,q0=T/b,s/b,y1/(17*b),17*y2/(B**3*s)
assert 17*p0*p0==b*(17-e0)*(17+3*e0)
assert 17*q0*q0==b*(s0*s0-e0*(17-b))*(s0*s0+3*e0*(17-b))

def points(p):return 1+sum(not((Y*Y-cubic(X,n))%p) for X in range(p) for Y in range(p))
def red(x,p):return x.numerator*pow(x.denominator,-1,p)%p
def add(a,b,p):
    if a is None:return b
    if b is None:return a
    x,y=a;X,Y=b
    if X==x and not((y+Y)%p):return None
    m=(((3*x*x+4*n*x-3*n*n)*pow(2*y,-1,p)) if X==x else ((Y-y)*pow(X-x,-1,p)))%p
    u=(m*m-2*n-x-X)%p
    point=(u,(m*(x-u)-y)%p)
    assert (point[1]**2-cubic(u,n))%p==0
    return point
def mult(k,a,p):
    b=None
    while k:
        if k&1:b=add(b,a,p)
        a=add(a,a,p);k//=2
    return b
P=red(x,53),red(y,53);R=mult(224,P,53)
assert P==(1,25) and R==(42,42) and mult(13,R,53) is None
assert points(5)==4 and points(53)==52 and (red(x,5),red(y,5))==(3,0)
assert 2304*n**6 %5 and 2304*n**6 %53
print(json.dumps(dict(x=str(x),y=str(y),r=str(r),u=str(u),v=str(v),b=str(b),B=str(B),T=str(T),s=str(s),
                      y1=str(y1),y2=str(y2),mod53=P,mod5=(3,0),projection224=R,projection_order=13,
                      count5=points(5),count53=points(53)),indent=2))
