#!/usr/bin/env python3
"""Exact split formal orbit check on the retained h; no expanded coordinates."""
from math import isqrt, prod
from pathlib import Path
import hashlib,json
f=Path(__file__).resolve().parent.parent/'rc-linked-four-pole-common-q-r1'/'ACTUAL-COMMON-Q-SCALAR-PREFIX.json'
data=f.read_bytes()
assert hashlib.sha256(data).hexdigest()=='5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7'
h=int(json.loads(data)['h'])
def factors(n):
    for p in range(2,isqrt(n)+1):
        if n%p:
            continue
        yield p
        while n%p==0:
            n//=p
    if n>1: yield n
def field(p,sqrt=None):
    m=p*p
    def mul(x,y):
        a,b=x;c,d=y
        return (a*c+2*b*d)%m,(a*d+b*c)%m
    sq=lambda x:mul(x,x)
    add=lambda x,y:((x[0]+y[0])%m,(x[1]+y[1])%m)
    neg=lambda x:((-x[0])%m,(-x[1])%m)
    sub=lambda x,y:add(x,neg(y))
    sc=lambda x,k:((x[0]*k)%m,(x[1]*k)%m)
    norm=lambda x:(x[0]**2-2*x[1]**2)%m
    inv=lambda x:sc((x[0],-x[1]),pow(norm(x),-1,m))
    unit=lambda x:bool(norm(x)%p)
    O=(0,0)
    sq2=(0,1) if sqrt is None else (sqrt,0)
    D=sq(sub((3,0),sq2))
    G=(add((1,0),sq2),sc(sq2,2))
    def project(X,Y,Z):
        if unit(Z):
            j=inv(Z); j2=sq(j)
            return mul(X,j2),mul(Y,mul(j,j2))
        assert unit(X) and unit(Y)
        return neg(mul(mul(X,Z),inv(Y))) # z=-x/y through the formal disk
    def is_form(P):return isinstance(P[0],int)
    def translate(P,z):
        # Invariant differential; valid mod p² because z∈pR.
        assert z[0]%p==z[1]%p==0
        x,y=P
        return add(x,mul(sc(y,2),z)),add(y,mul(sub(sc(sq(x),3),D),z))
    def dbl(P):
        if is_form(P):return sc(P,2)
        x,y=P
        L=sub(sc(sq(x),3),D)
        W=sc(mul(x,sq(y)),4)
        XX=sub(sq(L),sc(W,2))
        YY=sub(mul(L,sub(W,XX)),sc(sq(sq(y)),8))
        return project(XX,YY,sc(y,2))
    def sep(P,Q):
        x,y=P; X,Y=Q
        H=sub(X,x)
        S=sub(Y,y)
        V=mul(sq(H),x)
        C=mul(sq(H),H)
        XX=sub(sub(sq(S),C),sc(V,2))
        YY=sub(mul(S,sub(V,XX)),mul(C,y))
        return project(XX,YY,H)
    twodbl=dbl(G)
    assert not is_form(twodbl)
    def add_R(P):
        if is_form(P):return translate(G,P)
        x,y=P; X,Y=G
        H=sub(X,x)
        if unit(H) or unit(sub(Y,y)):return sep(P,G)
        S=sep(P,(X,neg(Y)))
        assert is_form(S)
        return translate(twodbl,S)
    def point(n):
        P=O
        for z in bin(n)[2:]:
            P=dbl(P)
            if z=='1':P=add_R(P)
            if is_form(P):
                assert P[0]%p==P[1]%p==0
            else:
                x,y=P
                assert sq(y)==sub(mul(sq(x),x),mul(D,x))
        return P
    def order(maybe=None):
        if maybe:
            for n in maybe:
                if is_form(point(n)):
                    for v in factors(n):
                        while n%v==0 and is_form(point(n//v)):n//=v
                    assert is_form(point(n)) and all(not is_form(point(n//r)) for r in factors(n))
                    return n
            raise ValueError('No certified order from candidate exponents')
        P=O
        for j in range(1,(p+1)**2+1):
            P=add_R(P)
            if is_form(P):return j
        raise ValueError('no first return')
    def U(P):
        if is_form(P):return sc(P,-2)
        x,y=P
        den=add(sq(x),D)
        return mul(sc(y,2),inv(den))
    return order,point,U,is_form

def row(p):
    assert all(p%d for d in range(2,isqrt(p)+1))
    assert p not in (2,3,7,17)
    rr=[x for x in range(p) if x*x%p==2]
    assert len(rr)==2 and rr[0]+rr[1]==p
    arms=[]
    for r in rr:
        sqrt=r+p*(((2-r*r)//p)*pow(2*r,-1,p)%p)
        assert sqrt**2%(p*p)==2
        order,point,U,formal=field(p,sqrt)
        o=order()
        assert h%o==0 and all(not formal(point(o//ell)) for ell in factors(o))
        n=h%(p*o)
        z=point(n)
        uh=U(z)
        assert formal(z) and uh[1]==0 and uh[0]%p==0 and uh[0]!=0
        arms.append(dict(root=r,hensel_root=sqrt,order=o,
                         reduced_h=n,formal_parameter=z[0],U_mod_p2=uh[0]))
    return dict(p=p,arms=arms,v_p_source_w37=2)
ps=(239,313,577,769,1489,1657,2039)
rows=[row(p) for p in ps]
a=(2,1,2399,407)
b=(1,1,-1,32)
gamma=(2,313*577*1489,2399,407)
def chi(n,p):
    v=pow(n%p,(p-1)//2,p)
    return 0 if v==0 else 1 if v==1 else -1
for k,(A,G) in enumerate(zip(a,gamma)):
    w=2 if k==0 else 1
    assert (A//w)%24==(G//w)%24 and chi(G,17)==chi(A,17) and chi(G,5)==chi(A,5)
for p in (313,577,1489):
    T=p-1
    assert pow(T,(p-1)//2,p)==1
    assert all(chi(G,p)==chi(A*T+B,p) for A,B,G in zip(a,b,gamma))
assert gamma[1]==268914889
print(json.dumps(dict(actual_h=str(h),split_depth_rows=rows,
                      necessary_symbol_candidate=gamma,
                      all_three_candidate_odd_primes_have_w37_depth_two=[313,577,1489]),indent=2))
