"""Exact arithmetic only. Independent of Lean and the author's fixtures."""
from fractions import Fraction as Q
from itertools import product
from math import prod

def place_class(x, p):
    if p == 0:
        return x < 0
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    if p == 2:
        return v % 2, x % 8
    return v % 2, pow(x % p, (p-1)//2, p)

def elliptic(x, n):
    return x*(x-n)*(x+3*n)

def xpair(x, n):
    return x+3*n, x-n

def squareclass_pair(z, p):
    return tuple(place_class(x,p) for x in z)

def subgroup(generators, p):
    return {
        squareclass_pair(tuple(prod(x[i] ** b for x,b in zip(generators,bits)) for i in (0,1)),p)
        for bits in product((0,1), repeat=len(generators))
    }

def table_test(n, bits, p):
    (s,i,j,k),(t,l,m,e)=bits
    sgn=lambda b:(-1)**b
    unit=lambda bit,tw,th:sgn(bit)*2**tw*3**th
    if p==0:
        return s==0
    if p==3:
        return m==0 and sgn(t)*2**l*n**e%3==1
    if p==n:
        residues={11:{1,3,4,5,9},23:{1,2,3,4,6,8,9,12,13,16,18}}[n]
        assert residues=={pow(k,2,n) for k in range(1,n)}
        return unit(s,i,j)%n in residues and unit(t,l,m)*sgn(e)%n in residues
    assert p==2
    return i==l==0 and sgn(t)*3**m*n**e%8 in (1,5)

base=tuple(product(product((0,1), repeat=4), repeat=2))
controls=0
for n,x,y,dyadic_x,pairref,roots in [
    (11,Q(75),Q(720),-76,(3,1),(Q(6),Q(8))),
    (23,Q(-69575,48**2),Q(27611155,48**3),-85,(1,-23),(Q(299,48),Q(73,48)))
]:
    assert y*y==elliptic(x,n)
    assert xpair(x,n)==tuple(c*r*r for c,r in zip(pairref,roots))
    torsion=((n,1),(3,-n))
    # Independent comparison to literal local generator subgroups before each filter.
    dyadic_generators=torsion+(xpair(dyadic_x,n),)
    assert place_class(elliptic(dyadic_x,n),2)==(0,1)
    sizes=[]
    remaining=set(base)
    for p in [0,3,n,2]:
        g=subgroup(dyadic_generators if p==2 else torsion,p)
        sizes.append(len(g))
        authoritative=set()
        proposed=set()
        for bits in base:
            labels=tuple((-1)**s*2**i*3**j*n**k for s,i,j,k in bits)
            if squareclass_pair(labels,p) in g:
                authoritative.add(bits)
            if table_test(n,bits,p):
                proposed.add(bits)
            controls+=1
        assert proposed==authoritative
        remaining &= proposed
        print(n,p,len(g),len(remaining))
    final={
        b for b in base
        if b[0][0]==b[0][1]==b[1][1]==b[1][2]==0 and b[1][0]==b[1][3]
    }
    assert sizes==[2,4,4,8] and len(remaining)==8 and final==remaining

def factor(n):
    p=2
    while p*p<=n:
        if n%p==0:
            exp=0
            while n%p==0:
                n//=p
                exp+=1
            yield p,exp
        p+=1
    if n>1:
        yield n,1

squarefree_checks=0
for n in range(11,25000,12):
    primes=list(factor(n))
    if any(e!=1 for _,e in primes):
        continue
    assert all(p>=5 for p,_ in primes)
    assert prod((-1)**((p-1)//2) for p,_ in primes) == -1
    assert n%24 in (11,23) and n%8 == (n%24)%8 and n%3==(n%24)%3
    squarefree_checks+=1
print(controls,'literal local pair comparisons;',squarefree_checks,'selected signed prime product checks')
