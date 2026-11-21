#!/usr/bin/env python3
"""Exact GL2(F13) density denominators for the joint transvection sieve."""
from itertools import product
from fractions import Fraction
import json
p=13
G=[(a,b,c,d) for a,b,c,d in product(range(p),repeat=4) if (a*d-b*c)%p]
U=[(a,b,c,d) for a,b,c,d in G if ((a+d)%p,(a*d-b*c)%p)==(2,1) and (a,b,c,d)!=(1,0,0,1)]
Z=[(a,b,c,d) for a,b,c,d in G if c==0 and a==d] # centralizer of [[1,1],[0,1]]
assert len(G)==26208 and len(U)==168 and len(Z)==156
assert len(G)==len(U)*len(Z)
assert Fraction(len(U),len(G))*Fraction(12,13)==Fraction(1,169)
rs={m:dict(zero_density=str(Fraction(1,13**m)),
    nonzero_projective_direction_density=str(Fraction(12,13**m)), directions=(13**m-1)//12)
    for m in range(1,6)}
assert all(int(r['directions'])*Fraction(r['nonzero_projective_direction_density'])+
           Fraction(r['zero_density'])==1 for r in rs.values())
print(json.dumps(dict(group_order=len(G),transvections=len(U),centralizer_order=len(Z),
    absolute_single_false_class_failure_density='1/169',
    relative_density_examples=rs),sort_keys=True,indent=2))
