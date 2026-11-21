#!/usr/bin/env python3
"""Exact CM fibre and isogeny-chain control; no original trace evaluation."""
from fractions import Fraction as Q
from itertools import product
from math import prod
import json


def f(a):
    if isinstance(a, tuple):
        return a
    return Q(a), Q(0), Q(0), Q(0)


def add(a,b):
    return tuple(x+y for x,y in zip(f(a),f(b)))


def neg(a):
    return tuple(-x for x in f(a))


def mul(a,b):
    c = [Q(0)]*4
    for i,x in enumerate(f(a)):
        for j,y in enumerate(f(b)):
            c[i^j] += x*y*(2 if i&j&1 else 1)*(3 if i&j&2 else 1)
    return tuple(c)


def sq(a):
    return mul(a,a)


def cub(a):
    return mul(sq(a),a)


def conj(a,k):
    return tuple((-x if (i&k).bit_count()%2 else x) for i,x in enumerate(f(a)))


def div(a,b):
    cof = prod_f(conj(b,k) for k in (1,2,3))
    N = mul(b,cof)
    assert N[0] != 0 and all(x==0 for x in N[1:])
    return mul(a,mul(1/N[0],cof))


def prod_f(xs):
    acc = f(1)
    for x in xs:
        acc = mul(acc,x)
    return acc


def value(coefs,x):
    y = f(0)
    for c in reversed(coefs):
        y = add(mul(y,x),c)
    return y


H12 = [-54000,1]
H48 = [6549518250000,-2835810000,1]
H192 = [-1080060886113159937649308593750000,
        826335556188178615474500000000,
        15705521635909735050750000,
        -8041801037378436000,1]

A = (Q(0),Q(1),Q(0),Q(0))
B = (Q(0),Q(0),Q(1),Q(0))


def cm_points():
    rows = []
    pp = set()
    for t,a,b in product((-2,2),(-1,1),(-1,1)):
        X = add(t//2,mul(a,A))
        x = add(3,mul(2*b,B))
        Y = mul(mul(4*b,B),sq(X))
        yh = div(add(add(Y,sq(sq(X))),1),2)
        assert sq(Y) == add(add(sq(sq(sq(X))),mul(14,sq(sq(X)))),1)
        assert add(X,neg(div(1,X))) == f(t)
        assert div(yh,sq(X)) == x
        u = add(add(X,-2),div(mul(3,X),yh))
        for d in (2,4,16):
            u = div(sq(u),add(u,d))
        j = div(cub(add(u,256)),sq(u))
        assert value(H192,j) == f(0)
        assert len(set(conj(j,k) for k in range(4))) == 4
        assert all(c.denominator == 1 for c in j)
        pp.add(j)
        rows.append({"t": t,"sqrt2_arm": a,"sqrt3_arm": b,
                     "t2": [str(c) for c in u],"j": [str(c) for c in j]})
    assert len(pp) == 4
    return rows


def pmul(a,b):
    c = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c


def padd(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
            for i in range(max(len(a),len(b)))]


def det(A):
    n=len(A)
    M=[list(map(Q,row)) for row in A]
    ans=Q(1)
    for i in range(n):
        j=next((j for j in range(i,n) if M[j][i]),None)
        if j is None:
            return 0
        if j!=i:
            ans=-ans
            M[j],M[i]=M[i],M[j]
        c=M[i][i]
        ans*=c
        for j in range(i+1,n):
            k=M[j][i]/c
            for t in range(i+1,n):
                M[j][t]-=k*M[i][t]
    assert ans.denominator == 1
    return int(ans)


def res(a,b):
    m,n=len(a)-1,len(b)-1
    rows = [[0]*k+a[::-1]+[0]*(n-1-k) for k in range(n)]
    rows += [[0]*k+b[::-1]+[0]*(m-1-k) for k in range(m)]
    return det(rows)


def edge_checks():
    ps=[256**3,3*256**2,3*256,1]
    p=[ps[0],ps[1],ps[2]-54000,1]
    norm48=padd(padd(pmul(ps,ps),[0,0]+[H48[1]*c for c in ps]),
                [0,0,0,0,H48[0]])
    qs=lambda x: [16**3,3*16**2-x,3*16,1]
    assert (16-256)**3//(-256) == 54000
    first=[]
    for x in range(4):
        d=res(p,qs(x))
        assert d == 2**24*x*value(H48,x)[0]
        first.append(d)
    second=[]
    for x in range(7):
        d=res(norm48,qs(x))
        assert d == 2**48*(x-54000)**2*value(H192,x)[0]
        second.append(d)
    return {"H_minus_12":H12,"H_minus_48":H48,"H_minus_192":H192,
            "first_resultant_samples":first,"second_resultant_samples":second}


print(json.dumps({"coefficient_basis": [1,2,3,6], "fibre": cm_points(),
                  "volcano": edge_checks()}, sort_keys=True, indent=2))
