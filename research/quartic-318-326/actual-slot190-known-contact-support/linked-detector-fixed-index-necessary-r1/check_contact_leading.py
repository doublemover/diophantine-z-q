#!/usr/bin/env python3
"""Exact quadratic-ring controls for the literal 16-step leading-weight order."""
from fractions import Fraction as F
import json
from math import prod

roots=(F(0),-F(1,2),-F(1),F(1,2399),-F(32,407))
# Weight powers at the literal 16 leaves of ActualDetectorFold318.
nus=(7,1,1,1,1,1,1,1,1,1,7,25,25,25,7,25)
ds={1:0,7:18,25:72}
def v(x,p):
    assert x
    a,b=abs(x.numerator),x.denominator
    i=0
    while a%p==0:
        a//=p;i+=1
    while b%p==0:
        b//=p;i-=1
    return i

def mod(x,m):
    return x.numerator*pow(x.denominator,-1,m)%m

def row(p,r,depth,scale,C,d):
    # The literal parameter T=s^2 t is close to this actual contact.
    T=r+p**depth
    delta=T-1
    f=prod(T-a for a in roots)
    e=v(f,p)
    assert v(delta,p)==0
    Wunit=F(scale**10)*delta**2*p**e/f
    # w37=p^d, hence the first coefficient is rational w37^2.
    coeff=[(F(p)**(2*d),F(0))]
    coeff += [(F(31*j+1,p**C),F(17*j+6,p**C)) for j in range(1,16)]
    m=p**5
    def mul(x,y):
        return ((x[0]*y[0]+2*x[1]*y[1])%m, (x[0]*y[1]+x[1]*y[0])%m)
    rho=7*e-2*d
    if rho<=0 or not 3*e>8*max(d,0)+C:
        return None
    a=(1,0)
    prev=0
    for i,nu in enumerate(nus):
        cur=(2**i)*rho
        leaf_u=Wunit**nu*delta**ds[nu]
        lin=[]
        for x in coeff[i]:
            if not x:
                lin.append(0); continue
            vx=v(x,p); E=cur-nu*e+vx
            assert E>=0
            lin.append(pow(p,E,m)*mod(x*F(p)**(-vx)*leaf_u,m)%m)
        square=mul(a,a)
        sf=pow(p,cur-2*prev,m)
        a=tuple((sf*x+y)%m for x,y in zip(square,lin))
        assert a[0]%p!=0 and a[1]%p==0
        prev=cur
    N=(a[0]**2-2*a[1]**2)%m
    Q=N*pow(2*a[0],-1,m)%m
    assert Q%p!=0
    y=v(f,p)-2*prev
    assert y<0 and y%2==e%2
    if d==C==0:
        assert y==-458751*e
    return p,str(r),depth,scale,C,d,e,y,list(a),Q

rows=[]
for p in (5,13,19,31,41,53,131):
    if any(r.denominator%p==0 or (r-1).numerator%p==0 for r in roots):
        continue
    if len({mod(r,p) for r in roots})!=len(roots):
        continue
    for r in roots:
        for s in (1,2,3):
            for depth,C,d in ((1,0,0),(2,0,0),(3,0,0),(4,1,1),(7,2,2),(4,1,-2)):
                study=row(p,r,depth,s,C,d)
                if study is not None:
                    rows.append(study)
assert len(rows)>500
print(json.dumps(dict(leaf_weight_powers=nus, controls=len(rows),rows=rows),
                 separators=(',',':')))
