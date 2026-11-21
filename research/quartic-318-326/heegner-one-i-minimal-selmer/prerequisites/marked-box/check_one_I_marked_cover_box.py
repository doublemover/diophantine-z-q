#!/usr/bin/env python3
"""Complete fixed-height search of the literal q119851 (β,1) quartic cover."""
from math import gcd,isqrt,prod
from hashlib import sha256
import json

B=(5,11,17,163,661,733,1489,1861)
beta=prod(B)
I=114649
q=119851
P=I*q
d=beta*P

def exact_roots():
    R=[0]; m=1
    for p in B:
        S=[s for s in range(p) if (s*s-P)*(s*s-9*P)%p==0]
        assert len(S)==4 and len(set(S))==4 and 0 not in S
        inv=pow(m,-1,p)
        R=[x+m*((y-x)*inv%p) for x in R for y in S]
        m*=p
    assert m==beta and len(R)==len(set(R))==4**len(B)
    return sorted(R)

def n2(u): return u[0]**2+u[1]**2
def red(r):
    v=(beta,0);u=(r,1)
    while True:
        if n2(u)>n2(v):u,v=v,u
        z=n2(u); s=u[0]*v[0]+u[1]*v[1]
        k=(2*s+z)//(2*z) # nearest integer (ties upward)
        if k==0:
            assert abs(u[0]*v[1]-u[1]*v[0])==beta
            assert n2(u)<=n2(v) and abs(2*s)<=z
            return u,v
        v=(v[0]-k*u[0],v[1]-k*u[1])

def ceildiv(a,b):return -((-a)//b)
def m_range(u,v,n,H):
    # Coordinate bounds 1≤(m u + n v)_i≤H.
    L=None; R=None
    for x,y in zip(u,v):
        y*=n
        if x==0:
            if not 1<=y<=H:return range(0)
            continue
        a,b=1-y,H-y
        if x<0:a,b=b,a
        l,r=ceildiv(a,x),b//x
        L=l if L is None else max(L,l)
        R=r if R is None else min(R,r)
    assert L is not None
    return range(L,R+1)

def search(H):
    cuts=(10**7,10**8,H)
    C={b:[0,0,0] for b in cuts}
    roots=exact_roots();solutions=[]
    for r in roots:
        u,v=red(r)
        N=H*(abs(u[0])+abs(u[1]))//beta
        for n in range(-N,N+1):
            for m in m_range(u,v,n,H):
                a=m*u[0]+n*v[0]; b=m*u[1]+n*v[1]
                assert 1<=a<=H and 1<=b<=H
                if gcd(a,b)!=1: continue
                assert gcd(b,beta)==1 and (a-r*b)%beta==0
                Z=max(a,b)
                n0=(a*a-P*b*b)*(a*a-9*P*b*b)
                assert n0%beta==0
                for X in cuts:
                    if Z<=X:C[X][0]+=1
                if n0<=0:continue
                n0//=beta
                for X in cuts:
                    if Z<=X:C[X][1]+=1
                s=isqrt(n0)
                if s*s!=n0:continue
                solutions.append((a,b,s))
                for X in cuts:
                    if Z<=X:C[X][2]+=1
    return C,solutions,sha256(b"".join(r.to_bytes(8,"little") for r in roots)).hexdigest()

def ell_count(p):
    N=1
    for x in range(p):
        y=x*(x-d)*(x+3*d)%p
        a=pow(y,(p-1)//2,p)
        assert a in (0,1,p-1)
        N+=1 if not a else 2 if a==1 else 0
    return N

def main():
    assert P==13740797299 and d==2811626664334219040035976315
    assert gcd(d,6)==1 and d%7 and d%53
    o7,o53=ell_count(7),ell_count(53)
    assert (o7,o53)==(8,52) and gcd(o7,o53)==4
    assert o53%7 and o7%53
    H=10**9
    C,found,hash0=search(H)
    print(json.dumps(dict(P=P,beta=beta,d=d,roots=4**8,root_digest=hash0,
                    bounds=C,primitive_positive_fraction_solutions=found,
                    good_reductions={"7":o7,"53":o53},
                    count_columns=["primitive_CRT_pairs","positive_product","cover_points"]),
                    indent=2,sort_keys=True))
if __name__=='__main__':main()
