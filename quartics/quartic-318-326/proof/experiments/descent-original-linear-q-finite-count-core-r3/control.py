#!/usr/bin/env python3
from fractions import Fraction as Q
from random import Random
from math import gcd
from itertools import product

def primes(n):
    return [p for p in range(2,n+1) if all(p%d for d in range(2,int(p**.5)+1))]
rng=Random(318326)
row=split=inert=mean=norms=packing=strict=selection=diag=0
for p in primes(31):
    for k in range(p+1):
        for z in range(3):
            S=rng.sample(range(p),k)
            rows=[[u for u in range(p) if all((u+c*v)%p for c in S)] for v in range(1,p)]
            assert all(len(r)==p-k for r in rows)
            assert sum(map(len,rows))==(p-1)*(p-k)
            row+=1
            w=Q(p,p-1)**(k+1)
            assert sum((w for r in rows for _ in r),Q(0))/p**2 == Q((p-1)*(p-k),p*p)*w
            mean+=1
    if p==2:
        continue
    for n in range(1,p):
        if p%4==1:
            bad=[x for x in range(1,p) if (x-1)*(n*pow(x,-1,p)-1)%p==0 or
                    (x+1)*(n*pow(x,-1,p)+1)%p==0]
            assert set(bad)=={t%p for t in (1,-1,n,-n)} and len(bad)<=4
            split+=p-1
        else:
            pairs=[(a,b) for a,b in product(range(p),repeat=2) if (a*a+b*b)%p==n]
            bad=[(a,b) for a,b in pairs if ((a-1)**2+b*b)%p==0 or ((a+1)**2+b*b)%p==0]
            assert len(pairs)==p+1 and set(bad)==({(1,0),(p-1,0)} if n==1 else set())
            inert+=len(pairs)
for _ in range(5000):
    N=rng.randrange(1,100)
    m=rng.randrange(1,50)
    A=Q(rng.randrange(1,100),rng.randrange(1,20))
    D=A*m*Q(rng.randrange(1,40),160)
    e=A*N*N/(4*m)
    lo=A*N*N/m
    med=D*N*N/(m*m)+e
    assert med+e<lo
    strict+=1

for _ in range(2000):
    Y=rng.randrange(5,19)
    s=rng.randrange(2,Y+1)
    ps=primes(19)
    # Signed positions; each plus norm has exactly two factors of 2.
    # Some points carry both medium and large hits, which are charged twice.
    good=[]
    total=medium=large=0
    for x in range(rng.randrange(1,8)):
        J=range(rng.randrange(1,5))
        f=[(64*rng.choice([p for p in ps if p>s]+[1]),
            4*rng.choice([p for p in ps if p>s]+[1])) for _ in J]
        hit={p for p in ps if p!=2 and any(n%p==0 and q%p==0 for (n,_),(_,q) in product(f,repeat=2))}
        w=rng.randrange(20)
        total+=w
        medium+=w*bool({p for p in hit if p<=Y})
        large+=w*bool({p for p in hit if p>Y})
        if not hit:
            assert all(gcd(n,q)==4 for (n,_),(_,q) in product(f,repeat=2))
            good.append(x)
        diag+=sum(n%p==q%p==0 for n,q in f for p in ps if p!=2)
        selection+=1
    if medium+large<total:
        assert good
for _ in range(10000):
    B=rng.randrange(3,1000)
    a,b=(rng.randrange(-B,B+1) for _ in range(2))
    if a*a+b*b<=B*B:
        assert (a+1)**2+b*b < 2*B*B
        packing+=1
    Qs=rng.randrange(1,20)
    u,q=(rng.randrange(-100,100) for _ in range(2))
    i,j=rng.sample([None]+list(range(-5,6)),2)
    def val(k):
        return q if k is None else u+k*Qs*Qs*q
    if i is None or j is None:
        v,r=val(i if i is not None else j),q
        v-=(i if i is not None else j)*Qs*Qs*r
    else:
        r,rem=divmod(val(i)-val(j),(i-j)*Qs**2)
        assert rem==0
        v=val(i)-i*Qs**2*r
    assert (v,r)==(u,q)
    norms+=1
print(f'{row} complete local supports, {mean} normalized means, {split} split fibres, {inert} inert fibres')
print(f'{selection} finite masked points ({diag} same-position hits), {strict} strict budgets, {packing} signed norm caps, {norms} affine inverses')
