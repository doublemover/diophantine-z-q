#!/usr/bin/env python3
"""Independent replay: explicit matrices, subgroup sets, alternate lattice enumeration."""
from itertools import product
from math import isqrt
import json
from pathlib import Path
import sys

source = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
brand = json.loads((source / "EVEN48-BRANDT-PACKET.json").read_text())
M = 16

def action(q, v):
    a, b, c, d = q
    x, y = v
    # Left multiplication by omega and J=(1+6omega) times conjugation,
    # in coordinates (1,omega). The two columns of J are (1,6),(5,-1).
    return ((a+c-6*d)*x+(-b+5*c+d)*y)%M, ((b+6*c-5*d)*x+(a-b-c+6*d)*y)%M

def subgroup(v):
    return frozenset(((j*v[0])%M,(j*v[1])%M) for j in range(1,M,2))

def q2(a, b):
    return a*a-a*b+b*b

def norm(p):
    rng = range(-p-1, p+2)
    E = [(a,b) for a,b in product(rng,repeat=2) if q2(a,b)<=p]
    return [x+y for x,y in product(E,repeat=2) if q2(*x)+q2(*y)==p]

reps = [tuple(v) for v in brand["orbit_representatives"]]
lines = {subgroup((a,b)) for a,b in product(range(M),repeat=2) if (a|b)&1}
units = norm(1)
assert len(units)==12
orbits = [{subgroup(action(q,v)) for q in units} for v in reps]
assert len(lines)==24 and set.union(*orbits)==lines and all(len(o)==6 for o in orbits)
assert orbits==[{subgroup(tuple(v)) for v in o} for o in brand["cyclic_subgroups_by_orbit"]]
for p,A in brand["hecke_matrices"].items():
    elems=norm(int(p))
    assert len(elems)==12*(int(p)+1)
    for i,v in enumerate(reps):
        images=[subgroup(action(q,v)) for q in elems]
        assert [sum(x in o for x in images) for o in orbits]==[12*x for x in A[i]]

def symbol(a,p):
    return 0 if a%p==0 else 1 if pow(a%p,(p-1)//2,p)==1 else -1

# Reindex the lattice enumeration: loop in b,c and solve exactly for d.
D=146965
B=19*D
sums=[0]*4
reps_count=0
for b in range(-isqrt(B//3),isqrt(B//3)+1):
    R=B-3*b*b
    if R%4:
        continue
    for c in range(-isqrt(R//3),isqrt(R//3)+1):
        r=R-3*c*c
        z=isqrt(r)
        if z*z!=r:
            continue
        for z0 in {z,-z}:
            if (c+z0)%2:
                continue
            d=(c+z0)//2
            reps_count+=1
            if b%19==c%19==d%19==0:
                continue
            # z19=(0,1,8); proportionality factor is c in the zero-polarization branch.
            beta=(-4*((2*c-d)+8*(2*d-c)))%19
            if beta==0:
                assert b%19==0 and d%19==(8*c)%19
            weight=symbol(c+d,3)*symbol(-beta if beta else c,19)
            if weight:
                for j,(x,y) in enumerate(reps):
                    X,Y=action((0,b,c,d),(x,y))
                    if (x*Y-y*X)%16==0:
                        sums[j]+=weight
assert reps_count==10944 and sums==[64,64,-64,-64]
coef=sum(x*y for x,y in zip(sums,(1,1,-1,-1)))
assert coef==256 and coef*coef//32==2048
print("24 lines; four size-six orbits; nine Hecke matrices; D0 10944 reps, weights",sums,"A(D0)",coef)
