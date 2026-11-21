#!/usr/bin/env python3
"""Fixed Gaussian search fixture only; exact squareclass character constraints."""
from itertools import product
from math import isqrt
import json
def prime(p):
    return p>=2 and all(p%q for q in range(2,isqrt(p)+1))
P=[]
for k,m in product(range(-25,26),repeat=2):
    a,b=57+112*k,80+112*m
    p=a*a+b*b
    if p>76176 and p%408==1 and prime(p):
        assert (a%16,b%16,a%7,b%7,p%7)==(9,0,1,3,3)
        P.append((p,a,b))
P=sorted(P)
assert len({p for p,a,b in P})==len(P)==13
assert [p for p,a,b in P[:3]]==[3162001,3641809,4247281]
Q=(5,7,11,13,19,23,29,31,37,41,43,53,61)
rank={}
rows=[]
for q in Q:
    assert prime(q) and 2<q<=76176
    row=sum((pow(p,(q-1)//2,q)==q-1)<<i for i,(p,a,b) in enumerate(P))
    rows.append(row)
    while row:
        k=row.bit_length()-1
        if k not in rank:
            rank[k]=row; break
        row^=rank[k]
assert len(rank)==len(P)
print(json.dumps({'fixed_gaussian_window':[-25,25],'primes_A_B':P,
                  'small_character_primes':Q,'character_row_masks':rows,
                  'kernel_dimension':0,'triad_each_negative_at_7':True},indent=2))
