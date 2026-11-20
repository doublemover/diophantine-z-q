#!/usr/bin/env python3
"""Exact packet for B3 and level 16; only fixed-size integer arithmetic."""
import itertools
import json
from math import gcd, isqrt


def n2(a,b):
    return a*a-a*b+b*b


def qm(t):
    a,b,c,d=t
    return n2(a,b)+n2(c,d)


def norm_elements(p):
    r=isqrt(4*p//3)
    return [z for z in itertools.product(range(-r,r+1),repeat=4) if qm(z)==p]


M=16
u=next((a,b) for a,b in itertools.product(range(M),repeat=2) if n2(a,b)%M==M-1)


def add(x,y):
    return tuple((a+b)%M for a,b in zip(x,y))


def scale(a,x):
    return tuple(a*b%M for b in x)


def mul(x,y):
    a,b=x
    c,d=y
    return ((a*c-b*d)%M,(a*d+b*c-b*d)%M)


def conj(x):
    a,b=x
    return ((a-b)%M,-b%M)


def ev(q,x):
    a,b,c,d=q
    return add(mul((a,b),x),mul((c,d),mul(u,conj(x))))


def key(v):
    a,b=v
    if a%2:
        return (1,pow(a,-1,M)*b%M)
    assert b%2
    return (pow(b,-1,M)*a%M,1)


def transform(q,v):
    return key(ev(q,v))


lines=sorted({(1,a) for a in range(M)}|{(a,1) for a in range(0,M,2)})
units=norm_elements(1)
assert len(units)==12
remaining=set(lines)
orbits=[]
while remaining:
    x=min(remaining)
    orbit=sorted(set(transform(q,x) for q in units))
    remaining.difference_update(orbit)
    orbits.append(orbit)
keys={v:i for i,orb in enumerate(orbits) for v in orb}
assert len(keys)==24
reps=[orb[0] for orb in orbits]
assert all(sum(transform(q,v)==v for q in units)*len(orb)==12 for v,orb in zip(reps,orbits))


def matrix(p):
    E=norm_elements(p)
    assert len(E)==12*(p+1)
    A=[]
    for orb in orbits:
        rs=set()
        for v in orb:
            raw=[keys[transform(q,v)] for q in E]
            assert all(raw.count(j)%12==0 for j in range(len(orbits)))
            rs.add(tuple(raw.count(j)//12 for j in range(len(orbits))))
        assert len(rs)==1
        A.append(tuple(rs)[0])
    assert all(sum(row)==p+1 for row in A)
    assert all(len(orbits[i])*A[i][j]==len(orbits[j])*A[j][i]
               for i,j in itertools.product(range(len(orbits)),repeat=2))
    return A


def aq(p):
    return -sum(0 if t%p==0 else (1 if pow(t%p,(p-1)//2,p)==1 else -1)
                for x in range(p) for t in [x*(x+1)*(x-3)])


def matvec(A,v):
    return tuple(sum(a*b for a,b in zip(row,v)) for row in A)


def emit():
    primes=[5,7,11,13,17,19,23,29,31]
    matrices={p:matrix(p) for p in primes}
    eigen=[v for v in itertools.product(range(-4,5),repeat=len(orbits))
           if any(v) and next(x for x in v if x)!=0 and next(x for x in v if x)>0
           and gcd(*v)==1
           and all(matvec(A,v)==tuple(aq(p)*x for x in v) for p,A in matrices.items())]
    assert len(eigen)==1
    f=eigen[0]
    j=(1,2,0,0)
    frob=[keys[transform(j,x)] for x in reps]
    assert all(f[frob[k]]==f[k] for k in range(len(f)))
    assert sum(len(orb)*x for orb,x in zip(orbits,f))==0
    return dict(local_norm_minus_one_unit=u,orbit_representatives=reps,
                cyclic_subgroups_by_orbit=orbits,hecke_matrices=matrices,
                eigenvalues={p:aq(p) for p in primes},primitive_eigenfunction=f,
                frobenius_permutation=frob)


if __name__=='__main__':
    print(json.dumps(emit(),indent=2,sort_keys=True))
