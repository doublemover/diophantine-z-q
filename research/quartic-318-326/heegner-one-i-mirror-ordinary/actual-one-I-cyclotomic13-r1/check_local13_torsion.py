#!/usr/bin/env python3
"""Literal ordinary 13-division ramification via unramified degree-12 mod-169 point arithmetic."""
from math import gcd
import sympy as sp
import json

p,n=13,12
d=2811626664334219040035976315
q=p**n

class Ring:
    def __init__(self,mod):
        self.m=mod
        self.zero=(0,)*n
        self.one=self.N(1)
        self.T=(0,1)+(0,)*(n-2)
    def N(self,a):return (a%self.m,)+(0,)*(n-1)
    def add(self,a,b):return tuple((x+y)%self.m for x,y in zip(a,b))
    def neg(self,a):return tuple((-x)%self.m for x in a)
    def sub(self,a,b):return self.add(a,self.neg(b))
    def sc(self,k,a):return tuple(k*x%self.m for x in a)
    def mul(self,a,b):
        c=[0]*(2*n-1)
        for i,w in enumerate(a):
            if w:
                for j,z in enumerate(b):c[i+j]+=w*z
        for k in range(2*n-2,n-1,-1):c[k-n]-=2*c[k]
        return tuple(x%self.m for x in c[:n])
    def pow(self,a,m):
        out=self.one
        while m:
            if m&1:out=self.mul(out,a)
            a=self.mul(a,a);m//=2
        return out
    def inv(self,a):
        if self.m==p:
            assert a!=self.zero
            v=self.pow(a,q-2)
        else:
            assert self.m==p*p
            v=FF.inv(tuple(w%p for w in a))
            v=self.mul(v,self.sub(self.N(2),self.mul(a,v)))
        assert self.mul(a,v)==self.one
        return v
    def div(self,a,b):return self.mul(a,self.inv(b))

FF=Ring(p);WW=Ring(p*p)
T=sp.symbols('T')
assert sp.Poly(T**12+2,T,modulus=p).is_irreducible

def sqrt_ff(a):
    if a==FF.zero:return FF.zero
    if FF.pow(a,(q-1)//2)!=FF.one:return None
    h,z=q-1,0
    while h%2==0:h//=2;z+=1
    j=next(FF.add(FF.T,FF.N(t)) for t in range(p) if FF.pow(FF.add(FF.T,FF.N(t)),(q-1)//2)!=FF.one)
    c,b,x,R=FF.pow(j,h),FF.pow(a,h),FF.pow(a,(h+1)//2),z
    while b!=FF.one:
        i=next(t for t in range(1,R) if FF.pow(b,2**t)==FF.one)
        v=FF.pow(c,2**(R-i-1))
        c=FF.mul(v,v);b=FF.mul(b,c);x=FF.mul(x,v);R=i
    assert FF.mul(x,x)==a
    return x

def cubic(x,r,a2,a4):
    return r.mul(x,r.add(r.mul(x,r.add(x,r.N(a2))),r.N(a4)))

def add(Q,R,r,a2,a4):
    if Q is None:return R
    if R is None:return Q
    x,y=Q;u,v=R
    if x==u:
        if r.add(y,v)==r.zero:return None
        assert y==v
        m=r.div(r.add(r.mul(x,r.add(r.sc(3,x),r.N(2*a2))),r.N(a4)),r.sc(2,y))
    else:m=r.div(r.sub(v,y),r.sub(u,x))
    a=r.sub(r.mul(m,m),r.add(r.N(a2),r.add(x,u)))
    b=r.sub(r.mul(m,r.sub(x,a)),y)
    assert r.mul(b,b)==cubic(a,r,a2,a4)
    return a,b

def scale(Q,k,r,a2,a4):
    R=None
    while k:
        if k&1:R=add(R,Q,r,a2,a4)
        k//=2
        if k:Q=add(Q,Q,r,a2,a4)
    return R

a2,a4=2*d,-3*d*d
e0,e1=2,-2
for i in range(2,n+1):e0,e1=e1,-2*e1-p*e0
card=q+1-e1
assert card%(p*p)==0 and card%(p*p*p)!=0 and pow(-2,n//2,p)==p-1
assert all(pow(-2,n//k,p)!=1 for k in (2,3))
cand=None
for t in range(p):
    x=FF.add(FF.T,FF.N(t))
    y=sqrt_ff(cubic(x,FF,a2,a4))
    if y is None:continue
    P=scale((x,y),card//p,FF,a2,a4)
    if P:
        assert scale(P,p,FF,a2,a4) is None and P[1]!=FF.zero
        cand=(t,P)
        break
assert cand is not None
trial,P=cand
x,y=P

def reduce(Q):
    if Q is None:return None
    return tuple(tuple(w%p for w in v) for v in Q)

def lifted_return(A4):
    assert A4%p==a4%p
    err=WW.sub(cubic(x,WW,a2,A4),WW.mul(y,y))
    assert all(w%p==0 for w in err)
    dy=FF.div(tuple(w//p for w in err),FF.sc(2,y))
    Y=WW.add(y,WW.sc(13,dy))
    assert WW.mul(Y,Y)==cubic(x,WW,a2,A4)
    W1=(x,Y)
    W2=add(W1,W1,WW,a2,A4)
    W4=add(W2,W2,WW,a2,A4)
    W8=add(W4,W4,WW,a2,A4)
    W12=add(W4,W8,WW,a2,A4)
    assert reduce(W12)==(x,FF.neg(y))
    u,v=W12
    A,B=WW.sub(v,Y),WW.sub(u,x)
    assert FF.zero!=tuple(t%p for t in A) and all(t%p==0 for t in B)
    C=WW.sub(WW.mul(A,A),WW.mul(WW.mul(B,B), WW.add(WW.N(a2),WW.add(x,u))))
    D=WW.sub(WW.mul(A,WW.sub(WW.mul(x,WW.mul(B,B)),C)),WW.mul(Y,WW.pow(B,3)))
    # The tangent parameter -x/y extends over the infinity chart; D is a unit here.
    jet=WW.div(WW.neg(WW.mul(B,C)),D)
    assert all(t%p==0 for t in jet)
    return [int(t//p) for t in jet]

rows=[lifted_return(a4+k*p) for k in range(p)]
zeros=[k for k,r in enumerate(rows) if not any(r)]
assert len(zeros)==1
out=dict(d=d,local_reduced_frob_poly=[1,2,13],frob_unit_order=12,
         field_polynomial='T^12+2',extension_cardinality=q,elliptic_point_count=card,first_nonzero_trial=trial,
         residue_torsion_generator=P,actual_t13P_div13_mod13=rows[0],
         tame_control_change_to_a4=13*zeros[0],test_rows_for_a4_plus_13k=rows,
         actual_inertia_order=12 if not any(rows[0]) else 12*13)
print(json.dumps(out,sort_keys=True,indent=2))
