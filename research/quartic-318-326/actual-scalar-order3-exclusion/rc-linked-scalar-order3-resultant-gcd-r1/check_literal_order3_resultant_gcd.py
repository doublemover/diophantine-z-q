#!/usr/bin/env python3
"""Exact literal ψ_{3h} intersected with the whole fixed-degree order-3 eliminant."""
from hashlib import sha256
from pathlib import Path
from functools import lru_cache
from math import gcd
import json, sys

h=473592745039516333133760
here=Path(__file__).resolve().parent
src=(Path(sys.argv[1]) if len(sys.argv)>1 else
     here.parent/'rc-linked-scalar-order3-resultant-r1'/'ORDER3-FIXED-RESULTANTS.json')
b=src.read_bytes()
assert sha256(b).hexdigest()=='1f7305f23e734423b129af730dad0469c224146acacd2c4ea50e065c7493bc16'
J=json.loads(b)
assert J["eliminant_degree"]==24
R=4376874610839020
beta=204618888056724185
A=17*144*beta

def exact_division_mod(M):
    # At n even, normalized e_n is ψ_n/(2y_0).
    # At odd n it is ψ_n. All arithmetic in Z/MZ[s]/(s²−2).
    def mul(x,y):
        a,b=x;c,d=y
        return ((a*c+2*b*d)%M,(a*d+b*c)%M)
    def add(x,y):return ((x[0]+y[0])%M,(x[1]+y[1])%M)
    def sub(x,y):return ((x[0]-y[0])%M,(x[1]-y[1])%M)
    def sc(k,x):return (k*x[0]%M,k*x[1]%M)
    def sq(x):return mul(x,x)
    def cube(x):return mul(sq(x),x)
    s=(0,1);x=(1,1);y=(0,2);d=(3,-1)
    a=sc(-1,sq(d));x2=sq(x);x4=sq(x2);x6=mul(x4,x2);a2=sq(a)
    psi3=sub(add(sc(3,x4),sc(6,mul(a,x2))),a2)
    even4=sc(2,sub(sub(add(x6,sc(5,mul(a,x4))),sc(5,mul(a2,x2))),mul(a,a2)))
    E4=sq(sq(sc(2,y)))
    @lru_cache(None)
    def q(n):
        assert n>=0
        if n==0:return (0,0)
        if n<3:return (1,0)
        if n==3:return psi3
        if n==4:return even4
        k,r=divmod(n,2)
        if r==0:
            return mul(q(k),sub(mul(q(k+2),sq(q(k-1))),mul(q(k-2),sq(q(k+1)))))
        u=mul(q(k+2),cube(q(k)))
        v=mul(q(k-1),cube(q(k+1)))
        return sub(u,mul(E4,v)) if k%2 else sub(mul(E4,u),v)
    numer3=q(3*h);numer=q(h)
    return numer3,numer,q.cache_info().currsize
out={}
for name,z in J['resultants'].items():
    M=int(z['exact_moving_resultant'])
    assert M>0 and gcd(M,2*3*7*R*(1+A)*beta)==1
    ah,ph,count=exact_division_mod(M)
    G=gcd(M,*ah)
    J0=gcd(G,*ph)
    removed=gcd(G,pow(J0,G.bit_length(),G)) if G>1 else 1
    rem=G//removed
    assert gcd(rem,J0)==1
    out[name]={"modulus_bit_length":M.bit_length(),"ring_cache_count":count,
      "both_3h_zero_gcd":str(G),"both_h_zero_gcd":str(J0),
      "saturated_order3_gcd":str(rem)}
print(json.dumps({"donor":sha256(b).hexdigest(),
    "h":h,"3h_bit_length":(3*h).bit_length(),"result":out},indent=2))
