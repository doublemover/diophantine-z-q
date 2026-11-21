"""Exact Q arithmetic at local weights, and modular (not rounded) fold tests."""
from fractions import Fraction as Q
from itertools import product
from math import prod

roots = (Q(0),Q(-1,2),Q(-1),Q(1,2399),Q(-32,407))
tags = (1,0,0,0,0,0,0,0,0,0,1,2,2,2,1,2)

def v(n,p):
    if not n:
        raise ValueError('valuation of zero tested separately')
    def ord(x):
        if x%p:
            return 0
        lo,hi=1,2
        while x%p**hi==0:
            lo,hi=hi,2*hi
        while lo+1<hi:
            o=(lo+hi)//2
            if x%p**o==0:
                lo=o
            else:
                hi=o
        return lo
    return ord(abs(n.numerator))-ord(n.denominator)

def residue(q,m):
    return q.numerator*pow(q.denominator,-1,m)%m

nval=nfold=0
for p, cexp, B, idx in product((2,3,17),(-1,0,1),(-2,0,2), (1,3)):
    m={2:3,3:1,17:2}[p]
    d=abs(B)+244*abs(cexp)+(p==2)+m+idx
    c=Q(p)**cexp*Q(5,7)
    A=Q(p)**d*7
    q=Q(1+(8 if p==2 else p)*idx)
    u=Q(1+(8 if p==2 else p)*(idx+2))
    D=A*A*q
    T=c*c*u/D
    f=tuple(u-r*D/c**2 for r in roots)
    F=prod(T-r for r in roots)
    Dlt=T-1
    W0=c**10*Dlt**2/F
    W=(W0,W0**7*Dlt**18,W0**25*Dlt**72)
    assert F==c**10/D**5*prod(f)
    assert [v(a,p) for a in f] == [0]*5 and v(q,p)==0
    assert v(Dlt,p)==2*cexp-2*d
    assert [v(a,p) for a in W] == [6*d+k*cexp for k in (4,64,244)]
    assert min(B+v(a,p) for a in W)>0
    nval+=1
    # Generic lower-envelope terms including exact zero coordinates.
    H=p**3
    x,y=1,0
    for j,r in enumerate(tags):
        e=W[r]*(Q(p)**B)*Q((idx+j)%5-1,7)
        f_=W[r]*(Q(p)**B)*Q((idx-j)%3-1,7)
        x,y=(x*x+2*y*y+residue(e,H))%H,(2*x*y+residue(f_,H))%H
    assert x%p==1 and y%p==0 and (x*x-2*y*y)%p==1
    tau=Q(x*x-2*y*y,2*x)
    assert v(tau,p)==-(p==2)
    root=tau/(A**5*q**3*Dlt**3)
    b=q*prod(f)*root**2
    assert v(root,p)==d-6*cexp-(p==2)
    assert v(b,p)==2*(d-6*cexp-(p==2))>=m
    nfold+=1
print(f'{nval} exact weight/contact valuations; {nfold} 16-step modular folds with exact dyadic correction and depth target')
