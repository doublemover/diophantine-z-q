#!/usr/bin/env python3
from fractions import Fraction
from math import gcd,prod
import json

R=4376874610839020
BETA=204618888056724185
K=1+2448*BETA
TESTS=(2952271997968816765,5566083893370034)

def jacobi(a,n):
    assert n>0 and n%2==1
    j=1
    a%=n
    while a:
        while a%2==0:
            a//=2
            if n%8 in [3,5]:j=-j
        if a%4==n%4==3:j=-j
        a,n=n%a,a
    return j if n==1 else 0
def isolate(B,Z):
    """Return B restricted to primes NOT dividing Z, without factoring."""
    if B==1:return 1
    return B//gcd(B,pow(Z,B.bit_length(),B))
def keep(B,Z):
    return B//isolate(B,Z)

def simple(U,V,Sh,Si,P0,fixed):
    B=isolate(abs(U),Sh*fixed)
    if B==1:return 1
    M=B**12
    V0=V%M; Si0=Si%M
    F=(R**25*P0**2*V0**2*Sh**2+U**6*Si0**2)%M
    D=B**4*gcd(V0,B**4)**2
    assert M%D==0
    return D//gcd(F,D)

def staged(U,V,Sh,Si,P0,fixed):
    B0=isolate(abs(U),Sh*fixed)
    if B0==1:return 1,[B0]
    v0=V%B0**3
    B1=keep(B0,gcd(v0,B0**3)//gcd(v0,B0**2))
    if B1==1:return 1,[B0,B1]
    M=B1**5
    g=gcd((P0%M)*(V%M)%M,M)
    r=gcd(g,B1**4)
    B=isolate(B1,(B1**4//r)*(g//r))
    if B==1:return 1,[B0,B1,B]
    v=V%B**8;p=P0%B**8
    f=(p*v)%B**8
    z=Si%B**5
    assert f%B**4==z%B==0
    G=(R**25*(f//B**4)**2*Sh**2+(U//B)**6*(z//B)**2)%B**4
    D=(gcd(v,B**4)//B**2)**2
    assert B**4%D==0
    return D//gcd(G,D),[B0,B1,B]

def val(a,p):
    e=0
    assert a
    while a%p==0:a//=p;e+=1
    return e

def leg(a,p):
    return jacobi(a,p)

def make(rows):
    # Rows are synthetic valuations, not alleged actual crossed primes.
    # Coordinates match the expected local divisibilities, and CRT creates
    # genuine arithmetic controls independently checkable via Fraction.
    U=prod(p**a for p,a,b,u,sh,j in rows)
    V=prod(p**b for p,a,b,u,sh,j in rows)
    P0=prod(p**u for p,a,b,u,sh,j in rows)
    Sh=prod(p**sh for p,a,b,u,sh,j in rows)
    Sbase=U
    X=0; M=1
    for p,a,b,u,sh,j in rows:
        if j is None:continue
        assert b>2*a and u+b==4*a and sh==0
        A=R**25*(P0*V//p**(4*a))**2*Sh**2
        B=(U//p**a)**6*(Sbase//p**a)**2
        if j==0:
            r=next(z for z in range(1,p) if (A+B*z*z)%p)
            mod=p
        else:
            r=next(z for z in range(1,p) if (A+B*z*z)%p==0)
            mi=p
            for k in range(j):
                r+=(-((A+B*r*r)//mi)*pow(2*B*r,-1,p)%p)*mi
                mi*=p
            r+=p**j; mod=mi
            assert val(A+B*r*r,p)==j
        X+=(r-X)*pow(M,-1,mod)%mod*M
        M*=mod
    Si=Sbase*X
    assert Si and gcd(Si//U,U)==1
    fixed=2*3*5*7*R*K*BETA*prod(TESTS)
    F=R**25*P0**2*V**2*Sh**2+U**6*Si**2
    # Exact raw scalar quotient, not either proposed receiver.
    raw=Fraction(12*F,K*R**29*U**4*V**2*Sh**2)
    den=raw.denominator
    den=isolate(den,fixed)
    a= simple(U,V,Sh,Si,P0,fixed)
    b,stages=staged(U,V,Sh,Si,P0,fixed)
    Pset=sorted(p for p,_,_,_,_,_ in rows if val(den,p)%2)
    assert Pset==sorted(p for p,_,_,_,_,_ in rows if val(a,p)%2)
    assert Pset==sorted(p for p,_,_,_,_,_ in rows if val(b,p)%2)
    assert all(jacobi(s,den)==jacobi(s,a)==jacobi(s,b) for s in TESTS)
    return dict(U=U,stages=stages,staged_denominator=b,
                odd_support=Pset,signs=[jacobi(s,b) for s in TESTS])

if __name__=='__main__':
    # Signed arithmetic canaries: chosen small primes for the synthetic rows
    # including exact tie, under, over, Sh exclusion, strict b=2a, b>4a.
    main=[(433,1,3,1,0,1),(97,2,5,3,0,2),(101,1,5,0,0,None),
          (103,1,2,2,0,None),(107,1,3,0,0,None),(109,1,3,2,0,None),
          (113,1,0,0,1,None),(127,2,0,0,0,None)]
    aux=[(239,2,6,2,0,3),(233,1,4,0,0,1),(257,1,3,1,0,0)]
    print(json.dumps(dict(scope="synthetic valuations, not literal source evaluations",
                          controls=[make(main),make(aux)]),indent=2,sort_keys=True))
