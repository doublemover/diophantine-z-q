#!/usr/bin/env python3
"""Exact phase, primitive oriented form, and Fourier-tail numerical margins."""
from fractions import Fraction as F
from math import prod,gcd,isqrt
import json
N=205042530; K=770
P=(2,3,5,7,11,37,2399)
assert N==prod(P)
cols=[]
for p in (415721,9807649):
    assert all(p%r for r in range(2,isqrt(p)+1))
    assert p%8==1
    def leg(a):
        return {0:0,1:1,p-1:-1}[pow(a%p,(p-1)//2,p)]
    row=[leg(a) for a in (-1,2,5,7,11)]
    assert row==[1,1,1,-1,1]
    assert leg(-K)==-1==prod(row)
    cols.append(dict(p=p,signs=row))
c=isqrt(N*N//K)+1
while gcd(c,N)!=1:c+=1
assert c==7389223 and c%2==1 and gcd(c,N)==1 and c*c*K>N*N
D=-4*K*c*c
mods=(4,3,5,7,11,37,2399)
bs=(0,2*c%3,0,0,0,18*c%37,2132*c%2399)
M=prod(mods);assert M==2*N
B=sum(b*(M//m)*pow(M//m,-1,m) for m,b in zip(mods,bs))%M
assert all(B%m==b for m,b in zip(mods,bs))
C,r=divmod(B*B-D,4*N)
assert r==0 and (B,C)==(399254240,399397441)
assert B*B-4*N*C==D and gcd(N,gcd(B,C))==1
q=F(1,100)
T=(1+q)/(1-q)**3-1
assert 0<T<1 and sum(F(6)**k/prod(range(1,k+1)) for k in range(5))>100
print(json.dumps(dict(level=N,imaginary_field='Q(sqrt(-770))',inert_phase_columns=cols,
                stable_anchor=dict(conductor=c,oriented_form=[N,B,C],discriminant=D,
                    positive_im_square=[K*c*c,N*N],local_B_remainders=dict(zip(mods,bs))),
                exact_fourier_tail_ratio_bound=str(T)),indent=2))
