#!/usr/bin/env python3
"""Direct finite action/signature check for exact p=13 point-field scope."""
from math import prod
import json

p=13
d=2811626664334219040035976315
primes=(5,11,17,163,661,733,1489,1861,114649,119851)
assert prod(primes)==d and (d%3,d%8,d%13)==(2,3,1)
assert 1+sum((y*y-x*(x-d)*(x+3*d))%p==0 for x in range(p) for y in range(p))==16
assert {pow(-2,i,p) for i in range(12)}==set(range(1,p))
assert {pow(2,i,p) for i in range(12)}==set(range(1,p))
S={(x,y) for x in range(p) for y in range(p)}-{(0,0)}
B=[(a,b,c) for a in range(1,p) for b in range(p) for c in range(1,p)]
I=[(a,b,c) for a,b,c in B if c==1]
split3=[(a,b,c) for a,b,c in I if a in {1,3,9}]
inertia3=[(a,b,c) for a,b,c in split3 if a==1]
def orb(P,G):
    x,y=P
    return {((a*x+b*y)%p,c*y%p) for a,b,c in G}
def decomposition(G,H):
    points=set(S); rows=[]
    while points:
        P=min(points); V=orb(P,G); W=orb(P,H)
        assert V<=points and len(V)%len(W)==0
        points-=V; rows.append((len(W),len(V)//len(W)))
    return sorted(rows)
result=decomposition(B,I)
assert result==[(12,1),(13,12)]
result3=decomposition(split3,inertia3)
assert result3==[(1,3)]*4+[(13,1)]*12
Fplus_det={c for a,b,c in B if a==1}
assert Fplus_det==set(range(1,p))
c_fixed=sum((x,y)==(x,-y%p) for x,y in S)
assert (c_fixed,(len(S)-c_fixed)//2)==(12,78)
lines={(1,0)}|{(x,1) for x in range(p)}
assert (sum(a in {(1,0),(0,1)} for a in lines),(len(lines)-2)//2)==(2,6)
assert (13**3-1)%13==12 and (3**3-1)%13==0
print(json.dumps({'d':d,'d_prime_product':list(primes),'at_13_ef':result,'at_3_ef':result3,'F_signature':[12,78],'line_signature':[2,6],'Fplus_det_surjective':True,'lambda_units_multiplicity':7,'ordinary_sum_terms':156*prod(q-1 for q in primes)},indent=2))
