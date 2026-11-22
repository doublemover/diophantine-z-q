#!/usr/bin/env python3
from itertools import product
import json

def kr(a,p):
    a %= p
    return 0 if a == 0 else 1 if pow(a,(p-1)//2,p)==1 else -1
G=list(product(range(2),repeat=3)); cc=(1,0,0)
chi=[v for v in G if v[0]]
def pairing(v,g):return sum(a*b for a,b in zip(v,g))%2
N={''.join(map(str,g)):sum(not pairing(v,g) for v in chi) for g in G}
assert N['000']==4 and N['100']==0 and all(N[''.join(map(str,g))]==2 for g in G if g not in [G[0],cc])
assert 241%5==1751%5==1
ray=[(a*a+b*b)%5 for a,b in [(0,1),(1,1),(-1,1)]]
assert ray==[1,2,2] and kr(2,5)==-1
fields={p:[kr(-20,p),kr(5,p),kr(6,p)] for p in (5,7,29,103,241)}
assert fields[5][0]==0 and fields[7][0]==1 and fields[29]==[1,1,1]
assert all(kr(-1751*q*pow(241,-1,5),5)==1 for q in (1,4))
print(json.dumps(dict(fixed_ray=ray,source_sqrt2_inert5=True,fixed_aux_and_coefficient_residues=fields,
 good_prime_four_quadratic_norm_group_ring=N,scope='static rows and group ring only; no original moving index or ideal'),sort_keys=True,separators=(',',':')))
