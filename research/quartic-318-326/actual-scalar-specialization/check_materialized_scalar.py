#!/usr/bin/env python3
"""Independent exact first-return orders and projective precision-two chart check."""
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import sys

s=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
J=json.loads((s/'EXACT-SCALAR-SPECIALIZATION.json').read_text())
W,=json.loads((s/'ACTUAL-THETA-MODULAR-ROWS.json').read_text())
R=4376874610839020
A=114444*R
ps=[2,*map(int,J['orders'])]

def v(a,p):
    k=0
    while a%p==0:
        k+=1
        a//=p
    return k

for p,orders in [(int(p),os) for p,os in J['orders'].items()]+[(6551,W['orders'])]:
    assert all(p%q for q in range(2,isqrt(p)+1)) and p not in (2,7)
    roots=[s for s in range(p) if s*s%p==2]
    assert len(orders)==(len(roots) if roots else 1)
    for t,expected in zip(roots or [None],orders):
        def c(x,y=0):
            return ((x+(t or 0)*y)%p,0 if t is not None else y%p)
        def add(a,b):
            return ((a[0]+b[0])%p,(a[1]+b[1])%p)
        def minus(a,b):
            return ((a[0]-b[0])%p,(a[1]-b[1])%p)
        def mul(a,b):
            return ((a[0]*b[0]+2*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
        def quotient(a,b):
            d=pow((b[0]**2-2*b[1]**2)%p,-1,p)
            return mul(a,(d*b[0]%p,-d*b[1]%p))
        g=(c(1,1),c(0,2))
        e=mul(c(3,-1),c(3,-1))
        assert mul(g[1],g[1])==mul(g[0],minus(mul(g[0],g[0]),e))
        def plus(P,Q):
            if P is None: return Q
            if Q is None: return P
            x,y=P; z,w=Q
            if x==z and add(y,w)==c(0): return None
            k=quotient(minus(w,y),minus(z,x)) if x!=z else quotient(minus(mul(c(3),mul(x,x)),e),mul(c(2),y))
            j=minus(minus(mul(k,k),x),z)
            return j,minus(mul(k,minus(x,j)),y)
        Q=g
        for i in range(1,expected):
            assert Q is not None
            Q=plus(Q,g)
        assert Q is None,(p,t,expected)

h0=lcm(64,*[o for os in J['orders'].values() for o in os])
assert v(h0,131)==0 and J['h0']==lcm(h0,131)==J['first_index']==J['first_passing_h']
B0=6**15*3**65536
need=J['h0']*prod(p**((15*v(R,p)+2)//2) for p in ps)
assert J['J']==need//gcd(need,B0)
shift=B0*J['J']
s=1+shift
assert s.bit_length()==J['n_label_bits']==104414
assert (2*(s-2)).bit_length()==104415
assert s%5==1 and 2*(s-2)%6==4
lo,hi=J['real_margin_tests'][0][2:]
one=1<<J['dyadic_interval_exponent']
assert 100*lo>one and 1000*hi<137*one

p=W['prime']
assert p==6551
m=p*p
Q=p**200
def lift_root(a):
    r=p
    while r<Q:
        a+=(-((a*a-2)//r)*pow(2*a,-1,p)%p)*r
        r*=p
        assert (a*a-2)%r==0
    return a

def projective_chart(g,a,n):
    # Weighted Jacobian (X:Y:Z), affine (X/Z²,Y/Z³). No affine
    # slope inversion. Dividing common weights spends at most 3 p-adic
    # digits each time; exact arithmetic rejects an unresolved endpoint.
    K=Q
    def normalize(P):
        nonlocal K
        X,Y,Z=[u%K for u in P]
        while K>m and X%(p*p)==0 and Y%(p**3)==0 and Z%p==0:
            X//=p*p; Y//=p**3; Z//=p; K//=p**3
        assert K>=m and (X%p or Y%p or Z%p)
        return X%K,Y%K,Z%K
    def double(P):
        X,Y,Z=P
        aa=X*X; bb=Y*Y; cc=bb*bb
        d=2*((X+bb)**2-aa-cc)
        e=3*aa+a*Z**4
        x=e*e-2*d
        return normalize((x,e*(d-x)-8*cc,2*Y*Z))
    x,y=g
    def mixed(P):
        X,Y,Z=P
        H=x*Z*Z-X; I=4*H*H; J=H*I
        r=2*(y*Z**3-Y); V=X*I
        u=r*r-J-2*V
        return normalize((u,r*(V-u)-2*Y*J,2*Z*H))
    P=(x,y,1)
    for bit in bin(n)[3:]:
        P=double(P)
        if bit=='1': P=mixed(P)
    X,Y,Z=P
    assert Z%p
    return (2*Y*Z)*pow((X*X-a*Z**4)%m,-1,m)%m

charts=[]
for r,o in zip([i for i in range(p) if i*i%p==2],W['orders']):
    e=lift_root(r)
    charts.append([projective_chart((1+e,2*e),-(3-e)**2,k%(p*o)) for k in (J['h0'],shift)])
assert [list(c) for c in zip(*charts)]==W['precision_two']['chart_coefficients']
u,w=zip(*charts)
r=pow(R,-1,m)
H=u[0]*u[1]%m
f=(u[0]**2+u[1]**2)*pow(2,-1,m)%m
I=w[0]*w[1]%m
q=I*pow(H*pow(R,15,m)%m,-1,m)%m
N=(1+(H*r)**2+2*f*r)%m
w=(N*N+R*q*q)%m
b=A*(w*pow(1+A,-1,m)%m)**2%m
delta=(1-b*pow(17,-1,m))%m
assert (H,I,w,b,delta)==(24196122,8185478,28798786,9656191,4480884)
assert delta==p*684 and pow(684,(p-1)//2,p)==1
print('15 original plus 2 later finite orders, exact h/J, interval margin and projective mod 6551² charts passed')
