#!/usr/bin/env python3
"""Exact finite supplemental control, not a proof of uniform distribution."""
import json
from itertools import product

PRIMES = (5, 13, 17, 29, 37, 41, 53, 61)


def cases(p):
    mod = lambda a: a % p
    square = {a*a % p for a in range(p)}
    non_square = next(a for a in range(p) if a not in square)
    values = list(product(range(p), repeat=2))
    one, z = (1, 0), (0, 0)
    def multiply(a, b):
        return ((a[0]*b[0]+non_square*a[1]*b[1]) % p, (a[0]*b[1]+a[1]*b[0]) % p)
    def minus(a, b):
        return ((a[0]-b[0]) % p, (a[1]-b[1]) % p)
    def neg(a):
        return minus(z, a)
    def divide(a, b):
        t = pow((b[0]*b[0]-non_square*b[1]*b[1]) % p, -1, p)
        return multiply(a, (t*b[0] % p, -t*b[1] % p))
    def plus(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        (x, y), (u, v) = P, Q
        if x == u and y == neg(v):
            return None
        if x == u:
            s = divide(minus(multiply((3, 0), multiply(x, x)), one), multiply((2, 0), y))
        else:
            s = divide(minus(y, v), minus(x, u))
        x3 = minus(minus(multiply(s, s), x), u)
        return (x3, minus(multiply(s, minus(x, x3)), y))
    def power(n, P):
        if n < 0:
            return power(-n, None if P is None else (P[0], neg(P[1])))
        R = None
        while n:
            if n % 2:
                R = plus(R, P)
            if n > 1:
                P = plus(P, P)
            n //= 2
        return R
    def primary(a, b):
        a -= 1
        for _ in range(3):
            if (a+b) % 2:
                return False
            a, b = (a+b)//2, (b-a)//2
        return True
    def frobenius(P):
        return None if P is None else tuple((x, -y % p) for x, y in P)
    ys = {}
    for y in values:
        ys.setdefault(multiply(y, y), []).append(y)
    points = [None]
    for x in values:
        points.extend((x, y) for y in ys.get(minus(multiply(x, multiply(x, x)), x), ()))
    norms = [(a,b) for a,b in product(range(-p,p+1),repeat=2) if a*a+b*b == p]
    chosen = []
    for i in range(p):
        if mod(i*i+1):
            continue
        [G] = [(a,b) for a,b in norms if mod(a+b*i) == 0 and primary(a,b)]
        a, b = G
        def action(a,b,P):
            turn = None if P is None else (neg(P[0]), multiply((i,0),P[1]))
            return plus(power(a,P),power(b,turn))
        Q = ((i,0), ((1-i) % p, 0))
        T = (z,z)
        assert plus(Q,Q) == action(0,2,Q) == T
        assert action(-2,2,Q) is None
        assert all(action(a,b,P) == frobenius(P) for P in points)
        chosen.append([i,a,b])
    assert len(chosen)==2
    return dict(p=p,w=non_square,points=len(points),cases=chosen,total=2*len(points))

result=[cases(p) for p in PRIMES]
print(json.dumps({"data":result,"total":sum(c["total"] for c in result)},sort_keys=True))
