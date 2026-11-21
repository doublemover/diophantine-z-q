#!/usr/bin/env python3
"""Standard-library exact contact graph / primitive norm / tangent replay."""
from math import gcd, isqrt, prod
from itertools import combinations
import json

def factor(n):
    n = abs(n)
    d = 2
    found = []
    while d*d <= n:
        if n % d == 0:
            found.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    return found + ([n] if n > 1 else [])

def l(a, p):
    res = pow(a % p, (p-1)//2, p)
    assert res in (0, 1, p-1)
    return -1 if res == p-1 else res

def isprime(p):
    return p > 1 and factor(p) == [p]

def edge(i, j, phase):
    return (phase == -1) ^ ((i,j) in {(1,4), (3,4)})

def primes(phase):
    graph = []
    for j in range(6):
        for p in range(409, 10_000_000, 408):
            if p in graph or not isprime(p) or l(7,p) != -1:
                continue
            if all(l(q,p) == 1-2*edge(i,j,phase) for i,q in enumerate(graph)):
                graph.append(p)
                break
        else:
            raise AssertionError(j)
    return graph

def v(n,p):
    assert n
    j = 0
    while n%p == 0:
        n //=p
        j +=1
    return j,n

def hilbert(x,y,p):
    a,u=v(x,p); b,w=v(y,p)
    return (-1)**(a*b*((p-1)//2)) * l(u,p)**b * l(w,p)**a

def tangents(A,D,z1,z2,z3,t):
    C = D*D-A
    e3 = A*(A+3*D*D)
    a0,b0=3*D*D-A,3*D
    R=a0*z1-C*b0*z3
    S=b0*z1-a0*z3
    assert a0*a0-C*b0*b0==e3
    assert R*R-C*S*S==e3*(z1*z1-C*z3*z3)
    assert (R-e3*t)*(R+e3*t)-C*S*S==e3*(z1*z1-C*z3*z3-e3*t*t)
    return z2-z3,R-e3*t,z1-2*A*t

def proof_control(phase):
    ps=primes(phase)
    d=prod(ps)
    beta=17*d
    assert all(l(p,17)==l(17,p)==1 for p in ps)
    assert all(l(ps[i],ps[j])==l(ps[j],ps[i])==1-2*edge(i,j,phase)
               for i,j in combinations(range(6),2))
    masks=[m for m in range(64) if all(
        sum(edge(min(i,j),max(i,j),phase)*(((m>>i)^(m>>j))&1)
            for j in range(6) if i!=j)%2==0 for i in range(6))]
    assert len(masks)==(16 if phase==1 else 8) and 63 in masks
    # Compact instances take Y=12 and vary only dyadic depth a=12*2^k.
    # The general family in the note permits arbitrary CRT-selected Y.
    for k in range(2048):
        a=12<<k
        A=beta*a*a
        D=d+17*(a//2)**2-36
        X=D-2*d
        C=D*D-A
        if D>0 and X>1 and gcd(A,D)==1 and (X-1)**2<C<X*X and prod(l(D,p) for p in ps)==-1:
            break
    else:
        raise AssertionError('compact norm witness')
    Y=12
    assert gcd(X,Y)==1 and C==X*X-d*Y*Y
    assert 0<A<D*D and isqrt(C)**2!=C
    for p,minimum in ((2,3),(3,1),(17,2)):
        u,U=v(17*A,p); vD,_=v(D,p)
        assert vD==0 and u>=minimum and u%2==0
        assert (U*pow(D,-2,8))%8==1 if p==2 else l(U,p)==1
    assert all(v(A,p)[0]==1 for p in ps)
    # A primitive norm identity certifies every p|C without factoring C.
    assert gcd(C,d)==gcd(C,Y)==1
    bits=[]
    for p in ps:
        s=D%p
        assert (s*s-C)%p==0
        L1,L2,L3=tangents(A,D,s,1,-1,0)
        assert (L1%p,L2%p,L3%p)==(2,6*D**3%p,D%p)
        sign=hilbert(L1,d,p)*hilbert(L2,1,p)*hilbert(L3,d,p)
        assert sign==l(D,p)
        bits.append(sign)
    assert prod(bits)==-1
    return dict(epsilon=phase,contact_primes=ps,lap_kernel_masks=masks,beta=beta,
                A=A,C=C,D=D,a=a,X=X,Y=Y,local_contact_signs=bits,
                cassels=prod(bits))

print(json.dumps({'scope':'literal profile arithmetic controls, not original fold outputs',
                  'cases':[proof_control(1),proof_control(-1)]},indent=2,sort_keys=True))
