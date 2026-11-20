#!/usr/bin/env python3
"""Exact arithmetic/small 2-descent on the surrogate; theta residues imported, not recomputed."""
from itertools import product
from math import gcd,isqrt,prod
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
b,th,m,q=17,409,455,19
C,E,Z=24,3079,62269
assert 17*C*C+th*E*E==Z*Z and gcd(C,Z)==gcd(E,Z)==1
assert 10000*(17*C)**2<Z*Z and Z%2==1 and Z%3!=0 and Z%b
assert q%24==19 and b%24==17 and th%24==1 and m%24==23
assert (5*7*13)==m
def prime(p):return p>=2 and all(p%r for r in range(2,isqrt(p)+1))
assert all(prime(p) for p in (b,q,th,5,7,13,53,37))
def leg(a,p):
    t=pow(a%p,(p-1)//2,p)
    assert t in (0,1,p-1)
    return -1 if t==p-1 else t
def bit(a,p):
    x=leg(a,p)
    assert x
    return int(x<0)
assert leg(b,th)==leg(th,b)==leg(q,b)==1
assert leg(q,th)==-1
assert all(leg(-m,p)==1 for p in (b,th,q))
assert leg(b,53)==leg(th,53)==1 and leg(m,53)==leg(q,53)==-1
M=24*b*th*53*m
assert gcd(q,M)==1

def selmer_control(P):
    n=prod(P);assert n%24==11 and leg(n,53)==-1
    s=[bit(-1,p) for p in P];la=[bit(3,p) for p in P]
    K=[[0 if p==r else bit(r,p) for r in P] for p in P]
    for i,row in enumerate(K):row[i]=sum(row)%2
    assert all(row[0]==0 for row in K)
    V=list(product((0,1),repeat=len(P)))
    vv=[]
    for z in (0,1):
        for u,v in product(V,V):
            if any((sum(r*a for r,a in zip(K[i],u))+la[i]*v[i]-z*la[i])%2 for i in range(len(P))):continue
            if any((sum(r*a for r,a in zip(K[i],v))+s[i]*v[i])%2 for i in range(len(P))):continue
            if sum((a+b)*c for a,b,c in zip(la,s,v))%2:continue
            vv.append((z,u,v))
    assert len(vv)==4 and all(z==0 and not any(v) for z,u,v in vv)
    assert n%37!=0
    c37=1+sum(1+leg(x*(x-n)*(x+3*n),37) for x in range(37))
    assert c37 in (32,44) and c37%13
    return dict(n=n,support=P,K=K,minus_one_bits=s,three_bits=la,
                positive_second_coordinate_candidate_vectors=vv,
                actual_local_class=(b,1),all_places_selmer_size=8,
                good_reduction_p37_cardinality=c37)
A=json.loads((HERE/'EXACT-TORIC-PAIR-Q19.json').read_text())
ret=[]
for j,P in enumerate(((b,q),(b,q,th))):
    row=selmer_control(P); n=row['n']
    a,c=A[2*j:2*j+2]
    assert (a['D'],c['D'],a['aux_l'],c['aux_l'])==(-n,m*n,37,-35)
    assert all(sum(z['raw_mod13_representatives_by_class'])%13==z['coefficient_mod13'] for z in [a,c])
    v=a['coefficient_mod13']*c['coefficient_mod13']
    S2=10*v*v%13
    assert S2==(4,9)[j]
    row.update(negative_coeff=a['coefficient_mod13'],positive_coeff=c['coefficient_mod13'],
               squared_raw_mod13_projection=S2)
    ret.append(row)
print(json.dumps(dict(beta=b,theta=th,m=m,q=q,n_variants=ret,
    same_reduced_congruence_class=[q,M],scalar_b_is_square_of=[17*C,Z],
    one_minus_b_over_17_is_theta_times_square_of=[E,Z],
    production_scalar=False),indent=2))
