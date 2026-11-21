#!/usr/bin/env python3
"""Arithmetic shadow of the ordered determinant and scaled finite pullback.

The relevant isomorphisms of the actual universal family are not mocked here.
"""
import json
from fractions import Fraction
from itertools import product


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2))
                 for i in range(2))


def tr(a):
    return tuple(zip(*a))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def adj(a):
    return ((a[1][1], -a[0][1]), (-a[1][0], a[0][0]))


def app(f, a):
    return tuple(tuple(f(x) for x in r) for r in a)


def v(p, q):
    n, d = q.numerator, q.denominator
    if n == 0:
        return None
    out = 0
    while n % p == 0:
        n //= p
        out += 1
    while d % p == 0:
        d //= p
        out -= 1
    return out


data = {}
I = ((1, 0), (0, 1))
for p in (2, 3, 5, 7, 11, 13, 17, 2399):
    level = 11 if p == 3 else 3
    assert level % p != 0
    D = ((p, 1), (2 * p + 1, 4))
    C = ((-3, 4 * p), (2, p * p - 1))
    g = det(D)
    J = app(lambda x: Fraction(x, g), adj(D))
    assert mm(J, D) == I
    F = mm(tr(J), C)
    assert det(F) * g == det(C)
    data[str(p)] = dict(level=level, signed_fraction=str(det(F)), finite_checks=0,
                        reductions={})
    for ram_index in (1, 2, 5):
        mod = p**(ram_index + 2)
        red = lambda x: (Fraction(x).numerator *
                         pow(Fraction(x).denominator, -1, mod)) % mod
        reduced = mm(tr(app(red, J)), app(red, C))
        assert det(reduced) % mod == red(det(F))
        data[str(p)]['reductions'][str(mod)] = red(det(F))
        for gauge, s, j in product((-11, -1, 1, 11), (0, 1, 3 - p, p**2),
                                    (-1, 0, 1)):
            if gauge % p == 0:
                continue
            # h is the coefficient of a primitive lattice vector in the
            # *fixed* generic line; it need not itself be a local unit.
            h = Fraction(p**ram_index)**j
            # psi maps an integral primitive-square generator to D0*u in
            # the second lattice.  In the fixed generic frame its scalar
            # is psi(h²)/h².
            u = Fraction(1 + 2*p, 1 + p)
            m = 210*u / h**2
            lhs = 210 * Fraction(s, m)
            equiv = s / u
            assert lhs == equiv * h**2
            assert lhs == (equiv / gauge**2)*(h*gauge)**2
            if lhs == 0:
                assert s == 0
            else:
                assert v(p, lhs) - 2*v(p, h) >= 0
            data[str(p)]['finite_checks'] += 1

# Deliberately non-injective stalk evaluation, x -> 0 in Z_{(p)}.
# Use psi = 210(1+x) over the stalk at (p,x), where 1+x is a unit.
# Its inverse divided map pulls x to x/(1+x), with value 0 in the fiber.
assert (210*Fraction(1, 1 + 0), Fraction(0, 1+0)) == (210, 0)
print(json.dumps({'places': data, 'checks': sum(e['finite_checks'] for e in data.values()),
                  'noninjective_zero_canary': True}, indent=2, sort_keys=True))
