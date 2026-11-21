#!/usr/bin/env python3
"""Two exact contact-phase controls for the simultaneous lift norms."""
from math import gcd,isqrt,prod
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
rows=json.loads((HERE/'PINNED-CONTACT-PROFILES.json').read_text())['profiles']

def jacobi(a,n):
    assert n>0 and n%2
    a%=n
    sign=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5):sign=-sign
        a,n=n,a
        if a%4==n%4==3:sign=-sign
        a%=n
    return sign if n==1 else 0

def prime(p):
    return p>=2 and all(p%x for x in range(2,isqrt(p)+1))

def strip(n,m):
    while gcd(n,m)>1:n//=gcd(n,m)
    assert gcd(n,m)==1
    return n

def local(x,p):
    e=0
    while x%p==0:e,x=e+1,x//p
    return e,x

def f(t): return t**4-t*t+1

def case(row):
    eps,ps=row['epsilon'],row['contact_primes']
    assert len(set(ps))==6 and all(prime(p) and p%408==1 and jacobi(7,p)==-1 for p in ps)
    for i,p in enumerate(ps):
        for j,q in enumerate(ps[i+1:],i+1):
            neg=(eps==-1) ^ ((i,j) in {(1,4),(3,4)})
            assert jacobi(p,q)==jacobi(q,p)==1-2*neg
    beta=17*prod(ps)
    p=ps[0]
    t0=next(r for r in range(1,p) if jacobi(f(r),p)==-1)
    mod=6*beta//p
    t=1+mod*((t0-1)*pow(mod,-1,p)%p)
    chi=[jacobi(f(t),q) for q in [3,17,*ps]]
    assert t%p==t0 and t%mod==1 and chi==[1,1,-1,1,1,1,1,1]
    F=f(t)
    k0=t*strip((1+t*t)//2,beta)
    assert gcd(k0,6*beta*F)==1
    j=1
    k=k0*(1+6*beta*F*j)
    a=12*t*k
    A=beta*a*a
    D=12*beta*k*k-F
    C=D*D-A
    B=A+3*D*D
    u,v=D-6*t*t,2*t*(1+t*t)
    r,s=D+2*t*t,2*t*(1-t*t)
    assert gcd(A,D)==gcd(u,v)==1
    assert D>0 and u>0 and 2*u-1>3*v*v>0
    assert 0<A<D*D and (u-1)**2<C<u*u
    assert C==u*u-3*v*v and B==3*(r*r+s*s)
    assert all(local(A,q)[0]==1 and D%q for q in [17,*ps])
    guards=[]
    for q,e in ((2,4),(3,2),(17,2)):
        ee,z=local(17*A,q)
        assert D%q and ee==e
        if q==2:
            assert z%8==1
        else:
            assert jacobi(z,q)==1
        guards.append([q,e,z%(8 if q==2 else q)])
    assert D%4==3 and jacobi(3*beta,D)==jacobi(F,3*beta)==prod(chi)==-1
    return dict(epsilon=eps,beta=beta,contact_primes=ps,t=t,k=k,
       D=D,A=A,C=C,B_over_3=B//3,f_mod_character_order=[3,17,*ps],f_characters=chi,
       primitive_C_norm=[u,v],gaussian_B_over_3=[r,s],
       source_scope='numerical Ready profile with varying theta, not original fold',
       ready_local_depths_and_units=guards,cassels=-1)

print(json.dumps([case(r) for r in rows],sort_keys=True,indent=2))
