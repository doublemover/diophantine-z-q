#!/usr/bin/env python3
"""Exact level arithmetic and finite-coordinate controls; not a Lean run."""
from itertools import product
from collections import Counter
from fractions import Fraction
import json

e3, e11 = 22, 12
N = 33
assert [(e3%3,e3%11),(e11%3,e11%11)] == [(1,0),(0,1)]
assert ((e3+e11)%N, (e3*e11)%N) == (1,0)
assert pow(e3,2,N)==e3 and pow(e11,2,N)==e11
assert 11%3 == 2 and 3%11 == 3
comparison = { (e3*x%N, e11*x%N):x for x in range(N) }
assert len(comparison)==N
for (a,b),x in comparison.items():
    assert (a+b)%N==x and a%11==0 and b%3==0

units11=sum((a*d-b*c)%11!=0 for a,b,c,d in product(range(11), repeat=4))
assert units11==(121-1)*(121-11)==13200
# Exact ramified residue model over F_9: a in the coefficient field,
# b in the square-zero radical; a is the unit test. Frobenius x ↦ x^3.
units3=sum(a!=(0,0) for a in product(range(3),repeat=2)
         for b in product(range(3),repeat=2))
assert units3==72
# ± acts on the pair diagonally. Separate quotients lose the relative sign.
assert units3*units11//2==475200
assert (units3//2)*(units11//2)==237600
# Small control shows 4*3−11=1 in every characteristic.
assert all((4*3-11)%p==1%p for p in (2,3,5,7,11,13,17,2399))
# Norm ring tests use the same rational embedding in simple Q cases.
def vp(a,p):
    a=abs(a)
    e=0
    while a and a%p==0:
        a//=p;e+=1
    return e
norm_gate={}
for p in (2,3,5,7,11,13,17,2399):
    rows=[]
    for N in (3,11,33):
        norm=Fraction(1,p**vp(N,p))
        rows.append([N,norm==1])
    norm_gate[p]=rows
    assert dict(rows)[11 if p==3 else 3]
    assert dict(rows)[33] == (p not in (3,11))
print(json.dumps(dict(crt_projectors=(e3,e11), relative_sheets=units11,
    coarse_joint_sheets=units3*units11//2,
    coarse_naive_product_sheets=(units3//2)*(units11//2),
    norm_gate=norm_gate),indent=2))
