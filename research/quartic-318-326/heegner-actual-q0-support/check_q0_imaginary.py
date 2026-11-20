#!/usr/bin/env python3
"""Exact small diagnostics for the ordinary imaginary class-number test."""
from math import gcd, isqrt
import json

def forms(D):
    assert D<0 and D%4==1
    out=[]
    for a in range(1,isqrt((-D)//3)+1):
        for b in range(-a,a+1):
            if (b*b-D)%(4*a):
                continue
            c=(b*b-D)//(4*a)
            if a>c or (b<0 and (abs(b)==a or a==c)) or gcd(a,b,c)!=1:
                continue
            out.append([a,b,c])
    return out

def bit(a,p):
    v=pow(a%p,(p-1)//2,p)
    assert v in (1,p-1)
    return int(v==p-1)

def rank(M):
    Q={}
    for row in M:
        r=sum(b<<i for i,b in enumerate(row))
        while r:
            j=r.bit_length()-1
            if j not in Q:
                Q[j]=r
                break
            r^=Q[j]
    return len(Q)

def v2(a): return (a&-a).bit_length()-1

def test(q,h,keep):
    T=145; P=[5,29,q]; D=-T*q
    U=[[0 if p==r else bit(r,p) for r in P] for p in P]
    R=[[0 if p==r else bit(p if p%4==1 else -p,r) for r in P] for p in P]
    for i in range(len(P)):
        U[i][i]=sum(U[i])%2
        R[i][i]=sum(R[j][i] for j in range(len(P)) if j!=i)%2
    assert R==U and all(sum(u)%2==0 for u in R+list(zip(*R)))
    H=[r[:2] for r in U[:2]]
    fs=forms(D)
    assert len(fs)==h and rank(H)==rank(U)
    assert (rank(H)==2)==(v2(h)==2)==keep
    return dict(theta=T,q=q,D=D,class_number=len(fs),two_valuation=v2(h),
                proper_reduced_forms=fs,redei=R,H=H,passes=keep)

print(json.dumps([test(7,16,False),test(43,12,True)],indent=2))
