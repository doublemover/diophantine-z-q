#!/usr/bin/env python3
"""Exact squarefree lower-level fixed involutions and actual mover signs."""
from itertools import product
from math import prod,isqrt
import json
P=(2,3,5,7,11,37,2399)
A=(1,-1,-1,1,-1,1,-1)
W=tuple(-a for a in A)
MOVE=(415721,9807649)
def prime(q):
    return q>=2 and all(q%k for k in range(2,isqrt(q)+1))
assert all(prime(q) for q in P+MOVE)
assert prod(P)==205042530
def L(a,q):
    if q==2:return 0 if a%2==0 else (1 if a%8 in (1,7) else -1)
    return {0:0,1:1,q-1:-1}[pow(a%q,(q-1)//2,q)]
rows=[]; fix=[]; forced=[]; common=[]
for bits in product((0,1),repeat=len(P)):
    d=prod(p for p,k in zip(P,bits) if k)
    if d==1:continue
    eps=prod(e for e,k in zip(W,bits) if k)
    tail=[(p,L(-d,p)) for p,k in zip(P,bits) if not k and p%2==1]
    bb=all(s==1 for _,s in tail)
    signs=[L(-d,q) for q in MOVE]
    rows.append(dict(d=d,eigen=eps,complement_tests=tail,fixed=bb,pilot_signs=signs))
    if bb:
        fix.append(d)
        if eps==1:
            forced.append(d)
            if signs==[-1,-1]:common.append(d)
assert len(rows)==127 and len(fix)==21 and len(forced)==13
assert sorted(common)==[770,369446,2662890,29291790]
sg=[dict(p=q,mod8=q%8,minus1=L(-1,q),primes=[L(p,q) for p in P]) for q in MOVE]
assert [r['primes'] for r in sg]==[[1,-1,1,-1,1,1,1],[1,1,1,-1,1,-1,1]]
assert all(r['minus1']==1 and r['mod8']==1 for r in sg)
w77=next(row for row in rows if row['d']==770)
assert w77['eigen']==1 and w77['fixed'] and w77['pilot_signs']==[-1,-1]
sq={q:next(x for x in range(q) if (x*x+770)%q==0) for q,_ in w77['complement_tests']}
print(json.dumps(dict(level=prod(P),primes=P,ap=A,pilot_phase_rows=sg,
                      all_nontrivial_W=sorted(rows,key=lambda r:r['d']),
                      fixed=sorted(fix),forced=sorted(forced),inert_in_both=sorted(common),
                      w770_explicit_sqrt_by_complement=sq),indent=2))
