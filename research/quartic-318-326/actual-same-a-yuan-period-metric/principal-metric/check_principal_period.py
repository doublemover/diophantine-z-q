#!/usr/bin/env python3
"""Exact principal Gram/real period/character identity controls."""
from fractions import Fraction as Q
from itertools import permutations, product
import json
from math import prod


def mm(a,b):
    return tuple(tuple(sum(x*y for x,y in zip(r,c)) for c in zip(*b)) for r in a)


def adj(a):
    return ((a[1][1],-a[0][1]),(-a[1][0],a[0][0]))


def scale(x,a):
    return tuple(tuple(x*y for y in r) for r in a)


def ident(d):
    return tuple(tuple(int(i==j) for j in range(d)) for i in range(d))


def det(a):
    return sum((-1)**sum(r[i]>r[j] for i in range(len(r)) for j in range(i+1,len(r)))
               *prod(a[j][k] for j,k in enumerate(r))
               for r in permutations(range(len(a))))


def unvec(x):
    return ((x[0],x[2]),(x[1],x[3]))


def vec(x):
    a,b,c,d=(*x[0],*x[1])
    return a,c,b,d


def betas(mu):
    return mm(mu,((0,0),(0,-1))),mm(mu,((0,1),(0,0)))


def pair(nu,x,y):
    a=mm(mm(nu,x),adj(y))
    return -a[0][0]-a[1][1]


T0=((210,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1))
mu0=((0,-210),(1,0))
roles={}
for r,s in product((-3,0,2),(0,1,4)):
    S=mm(((1,r),(0,1)),((1,0),(s,1)))
    Si=adj(S)
    assert det(S)==1 and mm(S,Si)==ident(2)
    M=mm(mm(S,mu0),Si)
    nu=scale(-Q(1,210),M)
    nuM=mm(nu,M)
    assert nuM==ident(2) and det(M)==210 and det(nu)==Q(1,210)
    vectors=list(zip(*T0))
    Ucols=tuple(vec(mm(mm(S,unvec(v)),Si)) for v in vectors)
    U=tuple(zip(*Ucols))
    for j,k,v in product(range(4),range(4),(-3,4)):
        if j==k:
            continue
        shear=tuple(tuple(int(a==b)+(v if (a,b)==(j,k) else 0)
                         for b in range(4)) for a in range(4))
        T=mm(U,shear)
        Tcols=list(map(unvec,zip(*T)))
        E=tuple(tuple(pair(nu,t,t1) for t1 in Tcols) for t in Tcols)
        assert abs(det(T))==210 and det(E)==1
        assert all(u.denominator==1 for r1 in E for u in map(Q,r1))
        for x,y in ((Q(2,7),Q(5,7)),(Q(-1,3),Q(11,2))):
            B=((x,0,1,0),(0,x,0,1),(y,0,0,0),(0,y,0,0))
            assert abs(det(mm(B,T)))==210*y*y
        for i,beta in enumerate(betas(M)):
            assert beta[0][0]==beta[1][0]==0
            for C in Tcols:
                assert pair(nu,beta,C)==C[i][0]
                assert pair(nu,scale(-1,beta),C)==-C[i][0]
        mat=tuple(zip(*((b[0][1],b[1][1]) for b in betas(M))))
        assert det(mat)==det(scale(-1,mat))==210
        roles.setdefault(f"{r},{s}",0)
        roles[f"{r},{s}"]+=1
print(json.dumps(dict(controls=roles,total=sum(roles.values()),
                      actual_discriminant=210),indent=2,sort_keys=True))
