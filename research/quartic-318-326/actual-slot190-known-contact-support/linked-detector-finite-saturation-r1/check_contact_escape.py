#!/usr/bin/env python3
"""Exact finite support checks on the unscaled original contact factors."""
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path
import hashlib,json

d=Path(__file__).resolve().parent.parent/'linked-detector-fixed-scalar-prefix-r1'
f=d/'EXACT-LABEL-GUARD-CONTROLS.json'
raw=f.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='56f3ea2c40490ef2144c337a91017b0de64b6e94e9c065b351308ca4627764d0'
pin=json.loads(raw); h=int(pin['h'])
assert h==2674919872696542982499708931469673481677031981460644968840448461939051165286720
assert pin['finite_residue_checks'][0]['rational_guard_mod_p']==[4,1,1,1]
q=pin['finite_residue_checks'][1]['p']
assert q==1041427

a=[2,1,2399,407]; b=[1,1,-1,32]
limited=[11,131,163,q,13,37,53,109,661,733,1861]
wide=sorted(limited+[7,439,1489,2399])
def chi(n,p):
    v=pow(n%p,(p-1)//2,p)
    return 0 if v==0 else 1 if v==1 else -1
def prime(p):
    return p>1 and all(p%r for r in range(2,isqrt(p)+1))
assert len(set(wide))==15 and all(prime(p) for p in wide) and prime(2399)
assert set(limited)<set(wide) and set((2,3,5,17)).isdisjoint(wide)
assert prod((11,37))==407
det=[[x*y2-x2*y for x2,y2 in zip(a,b)] for x,y in zip(a,b)]
wide_rows=[]
for p in wide:
    divides_lead=(407%p==0)
    eligible=(not divides_lead and chi(-32*407,p)==1)
    wide_rows.append([p,chi(-32*407,p),p%3,eligible])
    assert not eligible or p%3==1
assert [p for p,s,r,e in wide_rows if e]==[163,439,661,733,1489,1861,q]
# This authentic escape 5 is deliberately saturated; inserting it would not
# allow the single contact argument by itself.
assert chi(-32*407,5)==1 and 5%3==2

# More detailed (optional) arithmetic for the first three forms. Their leading
# coefficients 2,1,2399 have no factors in the LIMITED free-prime list.
# Do not use this baseline for the fourth: 11 and 37 are free there.
P=limited
assert all(gcd(prod(P),a[i])==1 for i in range(3))
assert all(gcd(prod(P),det[i][j])==1 for i in range(3) for j in range(3) if i!=j)
def primes_of_mask(M):
    return [p for j,p in enumerate(P) if M>>j&1]
tables=[]; masks=[]
for i in range(3):
    aa,bb=a[i],b[i]
    allowed=sum(1<<j for j,p in enumerate(P) if aa%p and chi(-bb*aa,p)==1)
    vals={}
    for M in range(1<<len(P)):
        if M&~allowed:continue
        t=prod(primes_of_mask(M))
        if t%24==1 and chi(t,17)==1:vals[M]=t
    masks.append(vals)
    tables.append(dict(eligible=primes_of_mask(allowed),admitted_squareclasses=sorted(vals.values())))
def test(i,x,j,y):
    if x&y:return False
    for p in primes_of_mask(x):
        if chi(a[j]*masks[j][y],p)!=chi(a[i]*det[i][j],p):return False
    for p in primes_of_mask(y):
        if chi(a[i]*masks[i][x],p)!=chi(a[j]*det[j][i],p):return False
    return True
R=[(x,y) for x,y in product(*masks[:2]) if test(0,x,1,y)]
triples=[(x,y,z) for (x,y),z in product(R,masks[2]) if test(0,x,2,z) and test(1,y,2,z)]
assert [len(m) for m in masks]==[4,16,4] and len(R)==7 and triples==[(0,0,0)]

# Exact rank-zero E2 auxiliaries: all primitive 2-adic residue pairs fail the
# sole positive nontrivial dual-isogeny quartic; and two good group counts.
S={x*x%16 for x in range(16)}
n=0
for x,y in product(range(16),repeat=2):
    if x%2 or y%2:
        assert (2*x**4+8*y**4)%16 not in S
        n+=1
counts={p:1+sum(y*y%p==(x*x*x-4*x)%p for x,y in product(range(p),repeat=2)) for p in [3,5]}
assert counts=={3:4,5:4} and n==192
print(json.dumps(dict(actual_h=pin['h'],small_free_primes=limited,
                      wide_free_prime_fourth_form_rows=wide_rows,
                      fourth_form_required_unit_residue_at_3=407%3,
                      first_three_form_mask_tables=tables,
                      survivors_after_two=[(masks[0][x],masks[1][y]) for x,y in R],
                      survivors_after_three=[[masks[i][v] for i,v in enumerate(r)] for r in triples],
                      E2_primitive_mod_16_rejections=n,E2_good_counts=counts),indent=2))
