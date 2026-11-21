#!/usr/bin/env python3
from itertools import combinations
from hashlib import sha256
from pathlib import Path
import json,sys
from collections import Counter

def minor(M,j):
    return [(v & ((1<<j)-1)) | ((v>>(j+1))<<j) for i,v in enumerate(M) if i!=j]

def rank(M):
    B={}
    for v in M:
        while v:
            k=v.bit_length()-1
            if k not in B:
                B[k]=v;break
            v^=B[k]
    return len(B)

def lap(a):
    v=a.copy()
    for i,b in enumerate(a):
        if b.bit_count()&1:
            v[i]^=1<<i
    return v

pairs=list(combinations(range(1,7),2))
tree={(i,i+1) for i in range(1,6)}
roster=Counter()
for mask in range(1<<len(pairs)):
    a=[0]*9 # 17=0, six genuine contacts=1..6, r0=7, q0=8
    def ed(i,j):
        a[i]^=1<<j;a[j]^=1<<i
    for v in (7,8):
        for i in (0,1): ed(i,v)
    ed(7,8)
    for bit,(i,j) in enumerate(pairs):
        old=bool(mask & (1<<bit))
        if old: ed(i,j)
        if old != ((i,j) in tree):
            r=len(a);v=r+1
            a.extend([0,0]);ed(r,v);ed(8,r)
            for u in (r,v):
                ed(i,u);ed(j,u)
    L=lap(a)
    assert all((v & 127).bit_count()%2==0 for v in L)
    C=minor(L,8);C[0]^=1
    B=minor(lap(minor(a,0)),7)
    assert rank(C)==len(C) and rank(B)==len(B)
    assert C[0]==1|(1<<7)
    roster[(len(a)-8)]+=1 # includes r0 but not q0

p=29
Z=(0,0);ONE=(1,0)
def elem(a):return (a%p,0)
def add(a,b): return ((a[0]+b[0])%p,(a[1]+b[1])%p)
def neg(a): return ((-a[0])%p,(-a[1])%p)
def sub(a,b): return add(a,neg(b))
def mul(a,b): return ((a[0]*b[0]+2*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def powr(a,n):
    r=ONE
    for i in bin(n)[2:]:
        r=mul(r,r)
        if i=='1':r=mul(r,a)
    return r
def div(a,b):
    assert b!=Z
    return mul(a,powr(b,p*p-2))
def ptadd(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;z,w=Q
    if x==z:
        if y==neg(w):return None
        assert y==w
        m=div(add(sub(mul(elem(3),mul(x,x)),mul(elem(4),x)),elem(-3)),mul(elem(2),y))
    else:m=div(sub(w,y),sub(z,x))
    r=sub(sub(add(mul(m,m),elem(2)),x),z)
    return r,sub(mul(m,sub(x,r)),y)

f=Path(sys.argv[1]).read_bytes()
assert sha256(f).hexdigest()=='8cfca028b915bd6c059853447faeb5c50bbee67f58ac4816e4b25f336bfcc85d'
P=R=None
for i,q in enumerate(json.loads(f)['phi_values']):
    x,y=map(tuple,q)
    assert mul(y,y)==mul(mul(x,add(x,ONE)),sub(x,elem(3)))
    P=ptadd(P,(x,y))
    R=ptadd(R,(x,y if i<5 else neg(y)))
assert P==((27,0),(0,16))
assert R==((7,0),(0,24))
RR=ptadd(R,R);RRRR=ptadd(RR,RR)
assert RRRR==((18,0),(0,19))
assert pow(17,14,29)==28
assert mul((0,9),(0,9))==elem(17)
r7=[(x,y,z) for x in range(-2,3) for y in range(-1,2) for z in range(-1,2)
    if x*x+3*y*y+12*z*z==7]
assert len(r7)==4 and all(z==0 for x,y,z in r7)
print(json.dumps({'base_reference_weighted_phi_mod29':R,'four_base_reference_mod29':RRRR,
                  'all_fixed_contact_graph_checks':sum(roster.values()),
                  'helper_count_histogram':dict(sorted(roster.items())),
                  'reference_analytic_Sha':1},indent=2,sort_keys=True))
