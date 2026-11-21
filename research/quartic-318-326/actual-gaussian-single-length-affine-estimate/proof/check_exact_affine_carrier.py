#!/usr/bin/env python3
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import gcd

def phi(m):
    return sum(gcd(j, m) == 1 for j in range(m))

count = west = hyb = factors = floors = 0
for W, F in [(2, 32), (6, 96), (30, 480)]:
    for a, n in product(range(3), [7, 10, 13]):
        vertices = list(product(range(2), repeat=a))
        for q in range(1, 6):
            J = min(4, n//q)
            for b in [1, W-1]:
                groups = defaultdict(list)
                for raw in product(range(1, n+1), *[range(1, J+1)] * (2*a)):
                    x, h, hp = raw[0], raw[1:1+a], raw[1+a:]
                    z = [x+q*sum(wj*(hj-hpj) for wj,hj,hpj in zip(w,h,hp)) for w in vertices]
                    w = tuple((v-1)//n for v in z)
                    assert all(-a <= t <= a for t in w)
                    p = tuple(W*(v-n*t)+b for v,t in zip(z,w))
                    assert all(W+b <= v <= W*n+b for v in p)
                    u = tuple(c%F for c in raw)
                    s = tuple((v-c)//F for v,c in zip(raw,u))
                    for v,o,t in zip(p,vertices,w):
                        base = W*(u[0]+q*sum(oj*(uj-upj) for oj,uj,upj in zip(o,u[1:1+a],u[1+a:]))-n*t)+b
                        assert v == base+F*W*(s[0]+q*sum(oj*(uj-upj) for oj,uj,upj in zip(o,s[1:1+a],s[1+a:])))
                    groups[(w,u)].append(p)
                    count += 1
                    west += any(t<0 for t in w)
                assert sum(map(len, groups.values())) == n*J**(2*a)
                for group in groups.values():
                    c = tuple(t%F for t in group[0])
                    assert all(tuple(t%F for t in p) == c for p in group)
                    mu = tuple(Fraction(t%7,7) for t in c)
                    prime = lambda t: Fraction((3*t+4)%11,3)
                    S = range(len(c))
                    A = sum(__import__('math').prod(prime(t)-m for t,m in zip(p,mu)) for p in group)
                    main = len(group)*__import__('math').prod(mu)
                    B = 0
                    for mask in product(range(2), repeat=len(c)):
                        value = sum(__import__('math').prod(mu[i] if mask[i] else prime(p[i]) for i in S) for p in group)
                        B += (-1)**sum(mask)*(value-main)
                    assert A == B
                    hyb += 1

for W, F, D, pad in [(2,32,32,[]),(6,32,32,[3]),(30,96,32,[3,5]),(30,480,96,[5]),(210,480,32,[3,5,7])]:
    assert F % D == 0
    alpha = Fraction(phi(W), W)
    for p in pad:
        alpha *= Fraction(p,p-1)
    assert alpha == Fraction(phi(D),D)
    factors += 1

for a,q,p in product([1,2],[1,2,3,5,7,14],[3,5,7,11]):
    V = list(product(range(2), repeat=a))
    others = list(product(range(p), repeat=a))
    h0 = [0]*a  # condition h'=0: paired moment marginals remain uniform
    r = range(p)
    for i,w in enumerate(V):
        for j,z in enumerate(V[i+1:],i+1):
            n0, n1, joint = 0, 0, 0
            for ys,x in product(others,r):
                u = (x+q*sum(wi*yi for wi,yi in zip(w,ys)) + i) % p == 0
                v = (x+q*sum(zi*yi for zi,yi in zip(z,ys)) + j) % p == 0
                n0 += u
                n1 += v
                joint += u and v
            assert n0 == n1 == p**a
            if q % p:
                assert joint == p**(a-1)
            factors += 1

for N,c,A in product([1,7,11,100,1000,10000], [1,2,9,12], [1,3,4,17]):
    from math import isqrt
    # y-fixed fine=ceil(c sqrt N); exact analogue of the source inequality.
    fine = isqrt(c*c*N)
    fine += fine*fine < c*c*N
    J = fine*fine//A
    l = Fraction(c*c,2*A)
    if l*N >= 1:
        assert J >= l*N
        floors += 1
print(f"{count} original points, {west} negative wraps, {hyb} exact disjoint cell cancellations")
print(f"{factors} exact conductor normalization / finite-field pair controls, {floors} stronger integer floor controls")
