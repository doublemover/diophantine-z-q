#!/usr/bin/env python3
"""Exact numerical guards on the same lower curve, and an independent p7 two-isogeny canary."""
import json
from fractions import Fraction as R
from math import comb, prod

def count(p):
    square=bytearray(p)
    for x in range(1,(p+1)//2):
        square[x*x%p]=1
    S=0
    for x in range(p):
        rhs=x*(x+76768)*(x-407)%p
        if rhs: S+=2*square[rhs]-1
    return p+1+S

def fn(n):return (R(n),R(0))
def add(X,Y):return (X[0]+Y[0],X[1]+Y[1])
def neg(X):return (-X[0],-X[1])
def sub(X,Y):return add(X,neg(Y))
def mul(X,Y,nu=-7):return (X[0]*Y[0]+nu*X[1]*Y[1],X[0]*Y[1]+X[1]*Y[0])
def pw(X,n):
    U=fn(1)
    for _ in range(n): U=mul(U,X)
    return U

def p7():
    A=fn(R(5,16)); B=(R(0),R(-1,32))
    roots=[(R(0),R(-1,4)), (R(1,8),R(1,8)), (R(-1,8),R(1,8))]
    for x in roots: assert add(add(pw(x,3),mul(A,x)),B)==fn(0)
    u=roots[1]
    s=(R(1,2),R(1,2))
    a=mul(fn(3),u); b=add(mul(fn(3),pw(u,2)),A)
    a1=mul(fn(-2),a); b1=sub(pw(a,2),mul(fn(4),b))
    Aq=sub(b1,mul(fn(R(1,3)),pw(a1,2)))
    Bq=sub(mul(fn(R(2,27)),pw(a1,3)),mul(fn(R(1,3)),mul(a1,b1)))
    assert Aq==mul(pw(s,4),A)==(R(5,32),R(-15,32))
    assert Bq==mul(pw(s,6),B)==(R(35,64),R(-9,64))
    assert add(sub(pw(s,2),s),fn(2))==fn(0)
    lam=(-1,6)
    m=3;p=7
    Ha0=sum((-1)**m*comb(m,j)**2*lam[0]**j for j in range(m+1))%p
    DHa0=sum((-1)**m*j*comb(m,j)**2*lam[0]**(j-1) for j in range(1,m+1))%p
    ha_jet=DHa0*lam[1]%p
    ks_jet=pow(2*lam[0]*(lam[0]-1),-1,p)*lam[1]%p
    assert [Ha0,DHa0,ha_jet,ks_jet]==[0,6,1,5]
    def z(x):return (x%p,0)
    def red(X):return (int(X[0]%p),int(X[1]%p))
    def fa(X,Y):return red(add(X,Y))
    def fs(X,Y):return red(sub(X,Y))
    def fm(X,Y):return red(mul(X,Y,3))
    def fp(X,n):
        U=z(1)
        for _ in range(n): U=fm(U,X)
        return U
    def fd(X,Y):
        assert Y!=z(0)
        return fm(X,fp(Y,p*p-2))
    def check(Q):
        x,y=Q
        return fp(y,2)==fs(fp(x,3),x)
    def en(Q):
        x,y=Q
        return (x,fs(z(0),y))
    def ea(Q,S):
        x,y=Q;u,v=S
        t=fd(fs(fm(z(3),fp(x,2)),z(1)),fm(z(2),y)) if Q==S else fd(fs(v,y),fs(u,x))
        X=fs(fs(fp(t,2),x),u)
        return X,fs(fm(t,fs(x,X)),y)
    def gamma(Q):
        x,y=Q
        X=fs(x,z(1))
        X1=fa(fa(X,z(3)),fd(z(2),X))
        Y1=fm(y,fs(z(1),fd(z(2),fp(X,2))))
        return fd(fa(X1,fd(z(1),z(3))),fp(z(4),2)),fd(Y1,fp(z(4),3))
    Q=((0,1),(3,5))
    G=gamma(Q)
    J=ea(ea(G,G),en(Q))
    F=tuple(fp(x,p) for x in Q)
    assert all(check(P) for P in (Q,G,J,F))
    assert G==((4,1),(3,6)) and J==en(F) and J!=F
    return {'simple_Hasse_derivative':DHa0,'oriented_Hasse_jet':ha_jet,
            'Legendre_KS_tangent':ks_jet,'point':Q,'gamma_point':G,
            'two_gamma_minus_one':J,'Frobenius':F}

def main():
    Np=(2,3,5,7,11,37,2399)
    M=prod(q+1 for q in Np)
    C=2**len(Np)
    G=1+M//12-C//2
    assert [M,C,G,2*G-2]==[630374400,128,52531137,105062272]
    ps=(415721,9807649)
    n=[count(p) for p in ps]
    assert n==[414744,9805732]
    print(json.dumps({'index':M,'cusps':C,'genus':G,'differential_degree':2*G-2,
     'point_count_controls':[{'p':p,'Eflat_Fp':v,'a_p':p+1-v,'p_mod_19':p%19,
       'supersingular_mark_ambient':(p-1)*M//12} for p,v in zip(ps,n)],'p7_independent_orientation':p7()},
     indent=2,sort_keys=True))
if __name__=='__main__':main()
