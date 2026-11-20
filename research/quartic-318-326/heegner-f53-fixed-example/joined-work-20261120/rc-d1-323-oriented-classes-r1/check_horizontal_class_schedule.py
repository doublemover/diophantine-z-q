#!/usr/bin/env python3
"""Exact O_{-455} ideal multiplication and fixed-orientation 20-label schedule.
No elliptic quotient coordinates, p=53 trace, or pi values are generated."""
from itertools import combinations
from math import gcd
from pathlib import Path
import json

D=-455
unit=((1,0),(0,1))
# Basis (1,w), with w=(1+sqrt(D))/2 and w²=w−114.
def egcd(a,b):
    if b==0:
        return abs(a), (1 if a>=0 else -1), 0
    g,u,v=egcd(b,a%b)
    return g,v,u-(a//b)*v

def product(x,y):
    u,v=x
    s,t=y
    return u*s-114*v*t,u*t+s*v+v*t

def hnf(vectors):
    index=gcd(*(a*d-b*c for (a,b),(c,d) in combinations(vectors,2)))
    x,y=0,0
    for a,b in vectors:
        g,u,v=egcd(y,b)
        x,y=u*x+v*a,g
    assert y>0 and index%y==0
    n=index//y
    return (n,0),(x%n,y)

def multiply(I,J):
    return hnf([product(x,y) for x in I for y in J])

def proper_reduce(a,b,c):
    assert b*b-4*a*c==D and gcd(a,b,c)==1
    while True:
        q=(a-b)//(2*a)
        b,c=b+2*a*q,c+b*q+a*q*q
        if a>c:
            a,b,c=c,-b,a
        else:
            if a==c and b<0:
                b=-b
            return (a,b,c)

def label(I):
    (a,z),(b,c)=I
    n=b*b+b*c+114*c*c
    assert z==0 and a%c==b%c==n%(a*c)==0
    # Norm(a X − (b+cw)Y)/Norm(I) matches I(a,b_form,c_form)
    # = (a,(-b_form+sqrt(D))/2), not the inverse-sign convention.
    return proper_reduce(a//c,-(2*b+c)//c,n//(a*c))

def prime_ideal(q,w):
    assert (w*w-w+114)%q==0
    return hnf([(q,0),(-w,1)])

generators={'a':(29,2,5),'b':(5,3,2),'c':(7,4,2)}
ideals={k:prime_ideal(q,w) for k,(q,w,_) in generators.items()}
principal=label(unit)
for k,(_,_,order) in generators.items():
    p=unit
    for j in range(1,order+1):
        p=multiply(p,ideals[k])
        assert (label(p)==principal)==(j==order)

reference=Path(__file__).resolve().parents[2]/'high-hom-1120/heegner-odd-residue-example/SELECTED-CANDIDATE-323-53.json'
ref=json.loads(reference.read_text())
d,N,beta=ref['d'],ref['level'],ref['orientation_root_mod_4N']
assert beta==60875 and (beta*beta-D)==185*4*N
assert d==323 and d*beta%96==1
w=(beta+1)//2
local=[(q,w%q,(1-w)%q) for q in [16,3,289,361]]
assert local==[(16,6,11),(3,0,1),(289,93,197),(361,114,248)]
assert all(gcd(r-s,m)==1 for m,r,s in local)
assert (d*w+(1-d)//2)%48==1
assert all(pow(-beta%p,(p-1)//2,p)==1 for p in (17,19))
for p,lifts in [(2,(0,1)),(3,(0,1)),(17,(8,10)),(19,(0,1))]:
    assert all((v*v-v+114)%p==0 and (v*v-v+114)%(p*p)!=0 for v in lifts)

rows=[]
p=unit
for i in range(5):
    for j,k in [(0,0),(1,0),(0,1),(1,1)]:
        I=p
        if j:
            I=multiply(I,ideals['b'])
        if k:
            I=multiply(I,ideals['c'])
        rows.append({'offset':[i,j,k],'relative_form':list(label(I))})
    p=multiply(p,ideals['a'])
assert len({tuple(r['relative_form']) for r in rows})==20
assert sorted(r['relative_form'] for r in rows)==sorted(ref['class_labels'])
arrows=[]
for i in range(4):
    arrows.append({'source':[i,0,0],'target':[i+1,0,0],'generator':'a'})
for i in range(5):
    for source,target,key in [((i,0,0),(i,1,0),'b'),((i,0,0),(i,0,1),'c'),((i,0,1),(i,1,1),'b')]:
        arrows.append({'source':list(source),'target':list(target),'generator':key})
assert len(arrows)==19 and {tuple(a['target']) for a in arrows}=={tuple(r['offset']) for r in rows}-{(0,0,0)}

print(json.dumps({'status':'EXACT_IDEAL_AND_LEVEL_SCHEDULE_ONLY_NO_PI_VALUES',
    'discriminant':D,'level':N,'orientation_beta_mod_2N':beta,
    'low_level_orientation_beta_times_d_mod_96':d*beta%96,'level_eigenvalues_mod_m':local,
    'generators_q_w_order':generators,'relative_vertices':rows,'arrows':arrows},indent=2))
