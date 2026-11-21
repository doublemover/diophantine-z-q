#!/usr/bin/env python3
"""Exact upper/lower of the full 2-Selmer at roots (0,d,9d), literal q119851."""
from fractions import Fraction as F
from math import isqrt,prod
from itertools import product
import json
support=(2,3,5,11,17,163,661,733,1489,1861,114649,119851)
S=(-1,*support)
d=prod(support[2:])
e=(0,d,9*d)
N=len(S)
assert d==2811626664334219040035976315
assert all(p>1 and all(p%i for i in range(2,isqrt(p)+1)) for p in support)

def cl(x,p):
    assert x
    q=F(x)
    if p==-1:return int(q<0)
    a,b=q.numerator,q.denominator;v=0
    while a%p==0:a//=p;v+=1
    while b%p==0:b//=p;v-=1
    if p==2:
        u=a*pow(b,-1,8)%8
        return (v%2) | (dict([(1,0),(7,1),(5,2),(3,3)])[u]<<1)
    u=a*pow(b,-1,p)%p
    s=pow(u,(p-1)//2,p);assert s in (1,p-1)
    return v%2 | (int(s==p-1)<<1)

def row(x,p):
    if x in e:
        vv=[x-y if x!=y else prod(x-z for z in e if z!=x) for y in e]
    else:
        vv=[x-y for y in e]
        if cl(prod(vv),p):return None
    h={-1:1,2:3}.get(p,2)
    return cl(vv[0],p) | (cl(vv[1],p)<<h)

def ins(D,x):
    while x:
        k=x.bit_length()-1
        if k in D:x^=D[k]
        else:
            D[k]=x
            return True
    return False

def sc_d(x):
    q=F(x)
    if q<0:return -1*sc_d(-q)
    # read rational global squareclasses only from values known supported
    m,n=q.numerator,q.denominator
    r=1
    for p in support:
        t=0
        while m%p==0:m//=p;t^=1
        while n%p==0:n//=p;t^=1
        if t:r*=p
    assert m==n==1
    return r

def pair_bits(a,b):
    ans=0
    for i,v in enumerate((a,b)):
        if v<0:ans |=1<<(N*i)
        v=abs(v)
        for j,p in enumerate(support,1):
            if v%p==0:
                assert v%(p*p)!=0
                v//=p;ans|=1<<(N*i+j)
        assert v==1
    return ans

def out(a):
    x,y=(prod(p for j,p in enumerate(S) if a>>(N*i+j)&1) for i in range(2))
    z=sc_d(x*y)
    return (x,y,z)

def main():
    G={}; places=[]
    for p in (-1,*support):
        h={-1:1,2:3}.get(p,2)
        goal={-1:1,2:3}.get(p,2)
        loc={}; witnesses=[]
        def candidates():
            yield from e
            for t in range(1,96):
                yield t;yield -t
            if p>0:
                for i in (1,2,3,4,5,-1,-2,-3,-4):
                    for t in range(1,33):
                        if t%p==0:continue
                        for z in e:
                            yield F(z)+F(t)*F(p)**i
                            yield F(z)-F(t)*F(p)**i
        for x in candidates():
            v=row(x,p)
            if v is not None and ins(loc,v):
                f=F(x)
                witnesses.append([f.numerator,f.denominator,v])
            if len(loc)==goal:break
        assert len(loc)==goal, (p,loc,witnesses)
        for a in range(1,1<<(2*h)):
            if any((a&v).bit_count()%2 for v in loc.values()):continue
            C=0
            for i,j in product(range(2),range(N)):
                if (a&(cl(S[j],p)<<(i*h))).bit_count()%2:
                    C|=1<<(N*i+j)
            ins(G,C)
        places.append(dict(p=p,local_dim=goal,witnesses=witnesses))
    free=[i for i in range(2*N) if i not in G]
    vv=[]
    for i in free:
        t=1<<i
        for k,v in sorted(G.items()):
            if (t&v).bit_count()%2: t|=1<<k
        assert all((t&v).bit_count()%2==0 for v in G.values())
        vv.append(t)
    tor=[]
    for x in (0,d):
        vals=(x-ei if x!=ei else prod(x-z for z in e if z!=ei) for ei in e[:2])
        tor.append(pair_bits(*(sc_d(v) for v in vals)))
    beta=204618888056724185
    q=119851;b=4921145;B=41579528353
    target=pair_bits(beta,-b*q)
    assert out(target)==(beta,-b*q,-B*q)
    assert all((target&v).bit_count()%2==0 for v in G.values())
    T={}
    for x in tor:ins(T,x)
    assert ins(T,target)
    print(json.dumps(dict(d=d,source_bad_places=S,root_coordinates=e,
        local=places,linear_rank=len(G),full_selmer_dimension=len(free),
        basis_triples=[out(t) for t in vv],ordered_split_target=out(target),
        torsion_classes=[out(t) for t in tor]),indent=2,sort_keys=True))
if __name__=='__main__':main()
