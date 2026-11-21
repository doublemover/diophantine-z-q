#!/usr/bin/env python3
"""Exact local conductor-16 class quotient and lattice control."""
from collections import Counter
from itertools import product
from math import gcd
import json

M=16

def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d)%M,(a*d+b*c+b*d)%M

def norm(x):
    a,b=x
    return a*a+a*b+b*b

units=[x for x in product(range(M),repeat=2) if norm(x)%2]
mu=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
triv={mul((a,0),z) for a in range(1,M,2) for z in mu}
def key(x):
    return min(mul(x,y) for y in triv)
S=sorted({key(x) for x in units})
assert len(units)==192 and len(triv)==24 and len(S)==8
E=key((1,0))
orders={u:next(k for k in range(1,9)
              if __import__('functools').reduce(mul,[u]*k,(1,0)) in triv)
        for u in S}
assert Counter(orders.values())=={1:1,2:3,4:4}
nm=Counter(norm(k)%8 for k in S)
assert nm=={1:2,3:2,5:2,7:2}
assert all(norm(mul(x,y))%8==norm(x)%8 for x in units for y in triv)
for a,b in product(range(M),repeat=2):
    eta=(a,b)
    # O8 = Z2 + 8 Z2 omega.  u x = eta conjugate(x).
    # (1+u)/2 preserves O8 iff the two numerators belong to 2 O8.
    one=((1+a)%M,b)
    e2=mul(eta,(8,-8))
    second=(e2[0],(e2[1]+8)%M)
    ok=all(x[0]%2==0 and x[1]==0 for x in (one,second))
    assert ok==(a%2==1 and b==0)
moduli=[m for m in range(1,24) if gcd(m,24)==1]
assert [m for m in moduli if m%3==1 and m%8==7]==[7]

print(json.dumps({
    "O0_mod16_units":len(units),
    "rational_times_global_units":len(triv),
    "ring_class_size":len(S),
    "norm_mod8_multiplicities":dict(sorted(nm.items())),
    "ray_classes":[{"unit":x,"order":orders[x],"norm_mod8":norm(x)%8} for x in S],
    "normalized_numerator_lattice": "O8 = Z2 + 8 Z2 omega; (1+eta*conj)/2 integral iff eta rational odd mod16",
    "absolute_q0_residue_mod24":7
},sort_keys=True,indent=2))
