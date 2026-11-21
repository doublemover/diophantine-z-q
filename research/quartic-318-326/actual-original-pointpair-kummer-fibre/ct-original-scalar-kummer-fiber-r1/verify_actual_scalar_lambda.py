#!/usr/bin/env python3
"""Independent finite source replay for the two literal lambda nonsquare sites."""
from math import isqrt
from pathlib import Path
import json
S=json.loads((Path(__file__).resolve().parent/'PINNED-SCALAR-FIBER.json').read_text())
h,J,R,N=[S[k] for k in ('h','J','R_input','N')]
shift=6**15*3**N*J
As=114444*R
beta=As//(17*12**2)
assert As==17*12**2*beta and h==473592745039516333133760
rows=[]
for src in S['normalizer_rows']:
    p,order=src['p'],src['annihilator']
    assert all(p%q for q in range(2,isqrt(p)+1))
    assert pow(2,(p-1)//2,p)==p-1
    O=None;z=(0,0);one=(1,0)
    def K(n):return (n%p,0)
    def plus(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
    def minus(a,b):return ((a[0]-b[0])%p,(a[1]-b[1])%p)
    def mul(a,b):return ((a[0]*b[0]+2*a[1]*b[1])%p,(a[1]*b[0]+a[0]*b[1])%p)
    def sq(a):return mul(a,a)
    def norm(a):return (a[0]**2-2*a[1]**2)%p
    def inv(a):
        n=pow(norm(a),-1,p)
        return a[0]*n%p,-a[1]*n%p
    d=sq((3,p-1))
    Q=((1,1),(0,2))
    def curve(P):
        return P is None or sq(P[1])==mul(P[0],minus(sq(P[0]),d))
    assert curve(Q)
    def add(P,T):
        if P is None:return T
        if T is None:return P
        x,y=P;u,v=T
        if x==u and plus(y,v)==z:return O
        if x==u:
            assert y==v
            slope=mul(minus(mul(K(3),sq(x)),d),inv(mul(K(2),y)))
        else:
            slope=mul(minus(y,v),inv(minus(x,u)))
        X=minus(minus(sq(slope),x),u)
        L=(X,minus(mul(slope,minus(x,X)),y))
        assert curve(L)
        return L
    def times(k):
        cur=O
        for b in bin(k)[2:]:
            cur=add(cur,cur)
            if b=='1':cur=add(cur,Q)
        return cur
    assert times(order) is None
    def chart(n):
        P=times(n%order)
        assert P is not None
        x,y=P
        den=plus(sq(x),d)
        return mul(mul(K(2),y),inv(den))
    U=chart(h);V=chart(shift)
    assert list(U)==src['chart_h'] and list(V)==src['chart_i']
    H,I=norm(U),norm(V)
    f=sq(U)[0]
    Qp=I*pow(H*R**15,-1,p)%p
    Np=(one[0]+(H*pow(R,-1,p))**2+2*f*pow(R,-1,p))%p
    W=(Np**2+R*Qp**2)%p
    assert W and (H,I,W)==(src['H'],src['I'],src['W'])
    D=(1+As)//p
    assert (1+As)%p==0 and D%p
    lambdau=3*beta*(12*W*pow(D,-1,p))**2%p
    assert pow(lambdau,(p-1)//2,p)==p-1
    rows.append(dict(p=p,annihilator=order,h_residue=h%order,shift_residue=shift%order,
        chart_h=U,chart_i=V,H=H,I=I,f=f,N=Np,Q=Qp,W=W,lambda_valuation=-2,
        lambda_stripped_unit=lambdau,lambda_squareclass='nonsquare'))
assert [r['W'] for r in rows]==[146,429536]
print(json.dumps(dict(scope='actual scalar lambda infinity obstruction only',h=h,beta=beta,places=rows),
    indent=2,sort_keys=True))
