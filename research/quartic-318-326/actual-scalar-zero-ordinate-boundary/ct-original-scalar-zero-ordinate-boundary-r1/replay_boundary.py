#!/usr/bin/env python3
from math import prod
from pathlib import Path
from fractions import Fraction as F
import json
P=Path(__file__).resolve().parent
panel=json.loads((P.parent/'ct-original-scalar-mestre-marked-selmer-r1'/'EXACT-MARKED-SELMER-ROWS.json').read_text())
K=panel['visible'];B=panel['beta'];U='P'
D=dict(zip(K,panel['true_d_stripped_bits']))
ell=dict(zip(K,panel['conditional_one_unseen']['aggregate_bits']))
def bit(p,x):
    if p==U:
        if x in (-1,3):return 0
        if x==2:return 1 # P=13 mod24
        return ell[x]
    if x==U:
        if p==3:return 0
        return ell[p]
    a=pow(x%p,(p-1)//2,p); assert a in (1,p-1)
    return int(a==p-1)
def rows(L):
    n=len(L);m=n+1; R=[]
    for i,p in enumerate(L):
        l=sum(bit(p,q)<<j for j,q in enumerate(L) if i!=j)
        z=l^(D.get(p,l.bit_count()%2)<<i)
        R += [z^(bit(p,3)<<n)^((bit(p,3)^bit(p,-1))<<(m+i)),
              (z<<m)^(bit(p,2)<<(m+n))^(bit(p,-1)<<(m+i))]
    R += [sum(bit(3,p)<<(m+i) for i,p in enumerate(L))^(1<<(m+n))]
    R += [sum(bit(p,-1)<<i for i,p in enumerate(L))^(1<<n)^(1<<(m+n))]
    R += [sum((bit(p,-1)^bit(p,2))<<i for i,p in enumerate(L)) ^
          sum(bit(p,-1)<<(m+i) for i,p in enumerate(L))]
    return R
def rank(vv):
    p={}
    for x in vv:
        while x:
            j=x.bit_length()-1
            if j in p:x^=p[j]
            else:p[j]=x;break
    return len(p)
R=rows(K);RR=rows(K+[U])
assert rank(R)==23 and rank(RR)==24
v=[255,15268065,55088560]
def contains(x,rs):return all((x&z).bit_count()%2==0 for z in rs)
assert rank(v)==3 and all(contains(x,R) for x in v)
def embed(x):
    a,b=x%8192,x//8192
    return ((a&4095) | ((a>>12)<<13)) + (((b&4095) | ((b>>12)<<13))<<14)
full=[*map(embed,v),7936]
assert rank(full)==rank([m%16384 for m in full])==4
assert all(contains(x,RR) for x in full)
def extract(x,k):
    L=K+([3] if k==0 else [2])
    return [p for i,p in enumerate(L) if (x>>(13*k+i))&1]
def sg(v):
    a,b=extract(v,0),extract(v,1)
    k=(2 in b)
    for p in K[8:]:
        if p in a:k^=bit(p,2)
        if p in b:k^=bit(p,6)
    s=prod(b);pf=[29,181,1346909,70850399941]
    return dict(r=prod(a),s=s,first_primes=a,second_primes=b,sign_before_Jacobi=(-1)**k,
        fixed_D_signs=[(-1)**bit(p,s) for p in pf])
tags=list(map(sg,v[1:]))
assert [e['s'] for e in tags]==[2952271997968816765,5566083893370034]
assert [e['sign_before_Jacobi'] for e in tags]==[-1,1]
assert [prod(e['fixed_D_signs']) for e in tags]==[1,-1]
assert F(1,4)*(F(1,4)-1)*(F(1,4)+3)==F(-39,64)
# Signs at 2,3,infinity, aggregate odd d. Remain distinct from analytic ranks.
signs=[[ -1,-1,-1,1 ],[1,-1,-1,1]]
assert [prod(x) for x in signs]==[-1,1]
print(json.dumps(dict(h=panel['h'],beta=B,visible_rows=R,one_unseen_rows=RR,
 positive_visible_basis=v,positive_one_unseen_basis=full,one_unseen_first_projection_rank=4,
 tests=tags,root_sign_local_parts=signs,
 scope='literal zero ordinate accepted, two local quartics, first marked row; no rational point or unknown denominator signs'),
 indent=2,sort_keys=True))
