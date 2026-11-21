from fractions import Fraction
from itertools import product
from random import Random

labels = same = budgets = 0
for k in range(2,16):
    other = lambda i: 1 if i==0 else 0
    tags = [(i,i,other(i)) for i in range(k)] + [(i,j,j) for i in range(k) for j in range(k) if i!=j]
    assert len(tags)==k*k and len({(i,j) for i,j,_ in tags})==k*k
    assert all(i!=j0 for i,j,j0 in tags)
    labels+=len(tags)
for p in (3,5,7,11,13,17,19,23,29,31,37,41,43):
    for a,b in product(range(p),repeat=2):
        hits=((a-1)**2+b*b)%p==0 and ((a+1)**2+b*b)%p==0
        assert hits==(a==0 and (b*b+1)%p==0)
        same+=1
rng=Random(318326)
for _ in range(6500):
    k=rng.randrange(2,8)
    primes=list(range(rng.randrange(1,12),rng.randrange(13,29)))
    U=list(range(rng.randrange(1,13)))
    hit={(u,p,i,j):rng.randrange(6)==0 for u,p,i,j in product(U,primes,range(k),range(k))}
    w=[Fraction(rng.randrange(0,11),rng.randrange(1,10)) for u in U]
    s=primes[len(primes)//5]
    Y=primes[3*len(primes)//5]
    medium=lambda u:any(hit[u,p,i,j] for p,i,j in product(primes,range(k),range(k)) if s<p<=Y)
    large=lambda u:any(hit[u,p,i,j] for p,i,j in product(primes,range(k),range(k)) if s<p and Y<p)
    sm=lambda u:any(hit[u,p,i,j] for p,i,j in product(primes,range(k),range(k)) if s<p)
    thin=[rng.randrange(3)==0 for u in U]
    tagged=sum(w[u] for u,p,i,j in product(U,primes,range(k),range(k)) if s<p<=Y and hit[u,p,i,j])
    assert sum(w[u] for u in U if medium(u))<=tagged
    assert all(sm(u)==(medium(u) or large(u)) for u in U)
    err=sum(w[u]*(medium(u)+large(u)+thin[u]) for u in U)
    if err<sum(w):
        assert any(w[u]>0 and not medium(u) and not large(u) and not thin[u] for u in U)
    budgets+=1
assert Fraction(5,2)+Fraction(7,100)+Fraction(24,200)==Fraction(269,100)
assert Fraction(5,64)<Fraction(1,10)
print(f'{labels} exact position tags, {same} odd sign-pair root checks, {budgets} exact overlap/endpoint/margin trials')
