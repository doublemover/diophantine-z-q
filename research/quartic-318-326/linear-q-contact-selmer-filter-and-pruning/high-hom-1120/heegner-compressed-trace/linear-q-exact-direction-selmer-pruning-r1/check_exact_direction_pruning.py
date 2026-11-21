#!/usr/bin/env python3
"""Construct exact same-pair norm directions on both independent Ready controls."""
from fractions import Fraction as F
from math import gcd, isqrt
from pathlib import Path
import argparse, json

arg=argparse.ArgumentParser()
arg.add_argument("contact_json",type=Path)
file=arg.parse_args().contact_json

def primes(limit):
    a=bytearray(b'\1')*(limit+1);a[:2]=b'\0\0'
    for i in range(2,isqrt(limit)+1):
        if a[i]:a[i*i::i]=b'\0'*((limit-i*i)//i+1)
    return [i for i in range(2,limit+1) if a[i]]

def chi(a,p):
    u=pow(a%p,(p-1)//2,p)
    return -1 if u==p-1 else u

def val(n,p):
    assert n
    e=0
    while n%p==0:n//=p;e+=1
    return e

def crt(a,m,b,n):
    return a+m*((b-a)*pow(m,-1,n)%n),m*n

def sqrat(x):
    return x>=0 and isqrt(x.numerator)**2==x.numerator and isqrt(x.denominator)**2==x.denominator

def bits(x):
    return abs(x).bit_length()

answers=[]
for row in json.loads(file.read_text())["cases"]:
    A,C,D,be=(row[n] for n in ("A","C","D","beta"))
    P=row["contact_primes"]
    assert gcd(A,D)==1 and C==D*D-A and D>0
    S=1
    for p in P:assert p%408==1 and val(A,p)==1;S*=p
    assert be==17*S and isqrt(A//be)**2*be==A
    V={x for x in range(1<<6) if all(
        sum(((x>>i)^(x>>j))&1 for j,q in enumerate(P) if j!=i and chi(q,p)==-1)%2==0
        for i,p in enumerate(P))}
    assert V==set(row["lap_kernel_masks"])
    r=(len(V)-1).bit_length()
    assert 1<<r==len(V)
    M=2*A*C*D
    a=0;modulus=M
    picks={"C": [],"A":[]}; used=set()
    DD=D*D
    fs={"A":lambda m:1-DD*C*m*m,
        "D":lambda m:1+2*C*m+DD*C*m*m,
        "C":lambda m:1+2*DD*m+DD*C*m*m}
    for side in ("C","A"):
        alive=V
        # Their Legendre rows are retained only on the actual contact kernel.
        for p in primes(50000):
            if any((p%24!=1,p in used,M%p==0,chi(be,p)!=1)):continue
            if side=="A" and chi(C,p)!=1:continue
            char=sum((chi(q,p)==-1)<<i for i,q in enumerate(P))
            killed={x for x in alive if (x&char).bit_count()%2}
            if not killed:continue
            root=next(m for m in range(p) if fs[side](m)%p==0)
            hin=next(root+j*p for j in range(p) if fs[side](root+j*p)%(p*p)!=0)
            assert fs["D"](hin)%p
            other="C" if side=="A" else "A"
            assert fs[other](hin)%p
            a,modulus=crt(a,modulus,hin,p*p)
            used.add(p);alive=alive-killed
            picks[side].append(dict(prime=p,dual_mask=char,m_residue_mod_p2=hin))
            if alive=={0}:break
        assert alive=={0} and len(picks[side])==r
    assert a>0 and a%M==0
    u,v,w=tuple(fs[s](a) for s in ("A","D","C"))
    assert DD*v*v-A*u*u==C*w*w
    assert min(abs(u),v,abs(w))>0
    assert all(gcd(z,M)==1 for z in (u,v,w))
    assert gcd(u,v)==gcd(u,w)==gcd(v,w)==1
    Ap,Dp,Cp=A*u*u,D*v,C*w*w
    assert gcd(Ap,Dp)==1 and Cp==Dp*Dp-Ap
    mu,mup,dp=F(A,DD), F(Ap,Dp*Dp), F(Cp,Dp*Dp)
    assert 0<mup<1 and sqrat(mup/mu) and sqrat(dp/(1-mu))
    assert all(val(Ap,p)==val(A,p) for p in [2,3,17]+P)
    assert all((Ap*pow(Dp,-2,p)-A*pow(D,-2,p))%p==0 for p in P)
    for side,data in picks.items():
        for hit in data:
            p=hit["prime"]
            if side=="C":
                assert val(Cp,p)==2 and val(Ap,p)==val(Dp,p)==0
                assert chi(4*Ap*Ap,p)==1
            else:
                assert val(Ap,p)==2 and val(Cp,p)==val(Dp,p)==0
                assert chi(-3*be,p)==1
    answers.append(dict(phase=row["epsilon"],beta=be,contact_kernel_dimension=r,
        exact_m=a,norm_direction_k=DD*a,chosen_rows=picks,
        numerator_denominator_delta_numerator_bits=[bits(i) for i in (Ap,Dp*Dp,Cp)],
        residual_beta_supported_kernel_dimensions=[0,0]))
print(json.dumps(dict(cases=answers,scope="two independent standalone Ready controls, not actual source-generated b"),indent=2,sort_keys=True))
