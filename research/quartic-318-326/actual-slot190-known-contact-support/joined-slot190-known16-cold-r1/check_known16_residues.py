#!/usr/bin/env python3
"""Independent direct T-residue verification; no bitmask or determinant use."""
from itertools import combinations, product
from math import isqrt, prod

leading = (2,1,2399,407)
constant = (1,1,-1,32)
all_primes = (5,7,11,13,37,53,109,131,163,439,661,733,1489,1861,2399,1041427)
special = (5,11,37,2399)

def squares(p):
    return {j*j%p for j in range(p)}
def sign(a,p):
    a%=p
    if not a: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def subsets(primes):
    return (frozenset(r) for k in range(len(primes)+1) for r in combinations(primes,k))

for p in all_primes:
    assert p>1 and all(p%q for q in range(2,isqrt(p)+1))
assert all((a*t+b)%7 for a,b in zip(leading,constant) for t in squares(7))

possible_first = []
for p in all_primes:
    if sign(-2,p)==1: possible_first.append(p)
d = [prod(s) for s in subsets(possible_first) if prod(s)%24==1 and sign(prod(s),17)==1]
assert set(d)=={1,1441,169752601,244613498041}
assert {v%5 for v in d}=={1}
t5 = {t for t in squares(5) if sign(2*t+1,5)==-1}
assert t5=={1}

def states(sat):
    moving = set(all_primes)-sat-{5,7}
    for i,(a,b) in enumerate(zip(leading,constant)):
        root = {p:(-b*pow(a,-1,p))%p for p in moving if a%p and sign(-a*b,p)==1}
        a_odd = a//(2 if i==0 else 1)
        base = a//prod(p for p in moving if a%p==0)
        need5 = sign(a if 5 in sat else a+b,5)
        yield [(v, {p:root[p] for p in s})
             for s in subsets(sorted(root))
             if (v:=base*prod(s))//(2 if i==0 else 1)%24==a_odd%24
                      and sign(v,17)==sign(a,17) and sign(v,5)==need5]

def compatible(rows):
    roots = {}
    for i,(gi,local) in enumerate(rows):
        for p,t in local.items():
            if p in roots: return False
            roots[p]=t
            assert (leading[i]*t+constant[i])%p==0
    return all(sign(gj,p)==sign(leading[j]*t+constant[j],p)
               for j,(gj,_) in enumerate(rows) for p,t in roots.items() if gj%p)

for sat in subsets(special):
    survivors=sorted(tuple(v for v,_ in row) for row in product(*states(sat)) if compatible(row))
    assert survivors==([(2,1,2399,407)] if sat==frozenset(special) else []), (sat,survivors)
    print(f"{','.join(map(str,sorted(sat))) or '-'}: {survivors}")
