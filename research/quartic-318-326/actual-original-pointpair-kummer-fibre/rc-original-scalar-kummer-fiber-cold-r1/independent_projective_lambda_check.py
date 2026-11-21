#!/usr/bin/env python3
"""Independent Jacobian-coordinate check of the original scalar lambda residues."""
import json
from math import isqrt
from pathlib import Path
from sys import argv

pin = json.loads(Path(argv[1]).read_text())
h, J, R, N = (int(pin[k]) for k in ('h', 'J', 'R_input', 'N'))
assert h == 473592745039516333133760 and N == 65536
beta, rem = divmod(114444 * R, 17 * 144)
assert (beta, rem) == (204618888056724185, 0)
rows = []
for datum in pin['normalizer_rows']:
    p, o = datum['p'], datum['annihilator']
    assert p > 3 and all(p % d for d in range(2, isqrt(p)+1))
    assert pow(2, (p-1)//2, p) == p-1
    zero, one = (0, 0), (1, 0)

    def k(a):
        return (a % p, 0)

    def plus(a, b):
        return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)

    def sub(a, b):
        return ((a[0]-b[0]) % p, (a[1]-b[1]) % p)

    def mul(a, b):
        return ((a[0]*b[0]+2*a[1]*b[1]) % p, (a[0]*b[1]+a[1]*b[0]) % p)

    def sc(a, b):
        return mul(k(a), b)

    def sq(a):
        return mul(a, a)

    def norm(a):
        return (a[0]**2 - 2*a[1]**2) % p

    def inv(a):
        return sc(pow(norm(a), -1, p), (a[0], -a[1]))

    d = sq((3, -1))
    base = ((1, 1), (0, 2), one)
    inf = (one, one, zero)

    def valid(P):
        x,y,z = P
        return sq(y) == sub(mul(sq(x), x), mul(d, mul(x, sq(sq(z)))))

    def dbl(P):
        x, y, z = P
        if z == zero or y == zero:
            return inf
        M = sub(sc(3, sq(x)), mul(d, sq(sq(z))))
        S = sc(4, mul(x, sq(y)))
        X = sub(sq(M), sc(2, S))
        Y = sub(mul(M, sub(S, X)), sc(8, sq(sq(y))))
        return (X, Y, sc(2, mul(y,z)))

    def add(P, Q):
        x,y,z = P; a,b,c = Q
        if z == zero: return Q
        if c == zero: return P
        z2,c2 = sq(z),sq(c)
        U, V = mul(x,c2),mul(a,z2)
        M, N = mul(y,mul(c,c2)),mul(b,mul(z,z2))
        H,L = sub(V,U),sub(N,M)
        if H == zero:
            return dbl(P) if L == zero else inf
        H2=sq(H); H3=mul(H,H2); Z=mul(H,mul(z,c))
        X=sub(sub(sq(L),H3),sc(2,mul(U,H2)))
        Y=sub(mul(L,sub(mul(U,H2),X)),mul(M,H3))
        return X,Y,Z

    assert valid(base)
    def multiple(n):
        acc, g = inf, base
        while n:
            if n % 2:
                acc = add(acc,g)
                assert valid(acc)
            g = dbl(g)
            assert valid(g)
            n //= 2
        return acc

    assert multiple(o)[2] == zero
    ih=h % o
    ii=pow(6,15,o)*pow(3,N,o)*J % o
    def chart(n):
        X,Y,Z=multiple(n)
        assert Z != zero
        return mul(sc(2,mul(Y,Z)),inv(plus(sq(X),mul(d,sq(sq(Z))))))
    U,V=chart(ih),chart(ii)
    H,I=norm(U),norm(V)
    tr=sq(U)[0]
    Rinv=pow(R,-1,p)
    u=(1+pow(H*Rinv,2,p)+2*tr*Rinv)%p
    v=I*pow(H,-1,p)*pow(Rinv,15,p)%p
    w=(u*u+R*v*v)%p
    s,rem=divmod(1+114444*R,p)
    assert rem==0 and s%p and w
    z=3*beta*(12*w*pow(s,-1,p))**2%p
    assert pow(z,(p-1)//2,p)==p-1
    assert [*U]==datum['chart_h'] and [*V]==datum['chart_i']
    assert (H,I,w)==(datum['H'],datum['I'],datum['W'])
    rows.append(dict(p=p,annihilator=o,indices=[ih,ii],charts=[U,V],
                     norm_rows=[H,I], W=w, lambda_depth=-2, lambda_stripped=z))
assert [row['lambda_stripped'] for row in rows]==[84,268311]
print(json.dumps(rows,indent=2,sort_keys=True))
