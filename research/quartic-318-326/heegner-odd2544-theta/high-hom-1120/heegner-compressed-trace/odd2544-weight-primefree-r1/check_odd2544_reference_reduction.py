#!/usr/bin/env python3
"""Exact reference arithmetic independent of the theta enumerator."""
import json
from math import gcd
from pathlib import Path
import sys

src=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
J=json.loads((src/'ODD2544-REFERENCE-COEFFICIENTS.json').read_text())
p=53
zero=(0,0)
one=(1,0)

def FF(a):
    return (a%p,0)

def add(a,b):
    return tuple((x+y)%p for x,y in zip(a,b))

def sub(a,b):
    return tuple((x-y)%p for x,y in zip(a,b))

def mul(a,b):
    return ((a[0]*b[0]+22*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)

def div(a,b):
    m=pow((b[0]**2-22*b[1]**2)%p,-1,p)
    return mul(a,(b[0]*m%p,-b[1]*m%p))

def cubic(x):
    return mul(x,mul(add(x,one),sub(x,FF(3))))

def plus(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P
    u,v=Q
    if x==u and add(y,v)==zero:return None
    if x==u:m=div(sub(sub(mul(FF(3),mul(x,x)),mul(FF(4),x)),FF(3)),mul(FF(2),y))
    else:m=div(sub(v,y),sub(u,x))
    a=sub(sub(add(mul(m,m),FF(2)),x),u)
    b=sub(mul(m,sub(x,a)),y)
    assert mul(b,b)==cubic(a)
    return a,b

def nsmul(n,P):
    Q=None
    while n:
        if n&1:Q=plus(Q,P)
        n>>=1
        P=plus(P,P)
    return Q

S=((21,0),(0,31))
T=((22,0),(0,15))
assert all(mul(y,y)==cubic(x) for x,y in [S,T])
assert nsmul(13,T) is None
assert nsmul(224,S)==nsmul(11,T)==((34,0),(0,33))

def leg(a,p):
    assert a%p
    t=pow(a%p,(p-1)//2,p)
    return 1 if t==1 else -1

for D,e in [(146965,1),(-323,-1)]:
    assert D%8==5 and gcd(D,2544)==1 and D%4==1
    assert (leg(D,3),leg(D,53),leg(D,29))==(1,e,1)
    # The type-II places are those where gamma(q)^r differs from W(q).
    gamma={2:-1,3:1,53:e}
    W={2:1,3:-1,53:1}
    powers={2:4,3:1,53:1}
    typeII={q for q in W if gamma[q]**powers[q]!=W[q]}
    assert typeII==({3} if D>0 else {3,53})
    assert W[2]*W[3]*W[53]*gamma[2]**4*gamma[3]*gamma[53]==(-1 if D>0 else 1)
    l=-323 if D>0 else 146965
    assert (-1)**int(3 in typeII)*leg(l,3)==-1
    assert (-1)**int(53 in typeII)*leg(l,53)==-1
    assert l*D==J['discriminant']==-47469695

assert J['primitive_53_root']==2 and {pow(2,i,53) for i in range(52)}==set(range(1,53))
A=sum(r['pos_D_coeff'] for r in J['class_output'])
B,C=[sum(r['neg_D_coeff_a_plus_i_b'][i] for r in J['class_output']) for i in (0,1)]
assert (A,B,C)==(-3312,0,-3312)
assert 5*5%13==8*8%13==12 and (5+8)%13==0
m1,m2=(B+5*C)%13,(B+8*C)%13
assert (A%13,m1,m2)==(3,2,11)
den=A*A*m1*m2%13
assert den==3 and 11**2*pow(den,-1,13)%13==10
print('Fixed signs, both conjugate reductions, literal P_ref and calibration factor 10 passed.')
