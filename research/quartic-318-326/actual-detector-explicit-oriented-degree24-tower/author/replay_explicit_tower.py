#!/usr/bin/env python3
"""Exact coefficient identities and fixed Frobenius controls; standard library only."""
import json
from fractions import Fraction


class Poly:
    """Sparse polynomial in x,s,q over Q."""
    def __init__(self, coefficients=0):
        if not isinstance(coefficients, dict):
            coefficients = {(0, 0, 0): coefficients}
        self.c = {m: Fraction(a) for m, a in coefficients.items() if a}

    @staticmethod
    def convert(a):
        return a if isinstance(a, Poly) else Poly(a)

    def __add__(self, other):
        out = self.c.copy()
        for m, a in self.convert(other).c.items():
            out[m] = out.get(m, 0) + a
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -a for m, a in self.c.items()})

    def __sub__(self, other):
        return self + (-self.convert(other))

    def __rsub__(self, other):
        return self.convert(other) - self

    def __mul__(self, other):
        out = {}
        for m, a in self.c.items():
            for n, b in self.convert(other).c.items():
                mn = tuple(i + j for i, j in zip(m, n))
                out[mn] = out.get(mn, 0) + a*b
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        ans = Poly(1)
        for _ in range(exponent):
            ans *= self
        return ans

    def __eq__(self, other):
        return self.c == self.convert(other).c

    def reduce(self, coordinate, exponent, rhs):
        assert all(m[coordinate] < exponent for m in rhs.c)
        out = self.c.copy()
        while (m := max(out, key=lambda a: a[coordinate], default=None)) is not None:
            if m[coordinate] < exponent:
                break
            v = list(m)
            v[coordinate] -= exponent
            coeff = out.pop(m)
            for n, d in rhs.c.items():
                term = tuple(i+j for i,j in zip(v, n))
                out[term] = out.get(term, 0) + coeff*d
                if out[term] == 0:
                    del out[term]
        return Poly(out)

    def substitute_q(self, value):
        assert all(k == 0 for (_, _, k) in value.c)
        return sum((Poly({(i,j,0): a})*value**k
                    for (i,j,k), a in self.c.items()), Poly())


x = Poly({(1, 0, 0): 1})
s = Poly({(0, 1, 0): 1})
q = Poly({(0, 0, 1): 1})
F = x**3 - 2*x**2 - 3*x
d_xF = 3*x**2 - 4*x - 3
R = s**3 + 6*s - (6*s-8)*q
T = 5*q**2 + (6-s**2)*q + 9
p6 = s**6 - 8*s**5 - 60*s**4 - 720*s**2 + 1152*s - 576
rel_s = s**6 - p6
rel_x = s*x - q
assert ((x**2+3)**2 - 4*(s-x)*F).reduce(0,2,rel_x) == R*x+T
assert (-4*F+2*d_xF*(2*x-s)-(2*x-s)**3).reduce(0,2,rel_x) == R
assert (5*(s**3+6*s)**2 + (6-s**2)*(s**3+6*s)*(6*s-8)
        + 9*(6*s-8)**2) == -p6

q_in_s = (9*s**5 - 60*s**4 - 620*s**3 - 360*s**2 - 6960*s + 3888)*Fraction(1,2800)
assert R.substitute_q(q_in_s).reduce(1,6,rel_s) == 0
assert T.substitute_q(q_in_s).reduce(1,6,rel_s) == 0
S = s**3 - 3*s*q - 2*(s**2 - 2*q) - 3*s
K = s**2 - q - 2*s - 3
H = s**2 - 4*q
assert (2*F-S-(2*x-s)*K).reduce(0,2,rel_x) == 0
# alpha*bar(alpha)=5H(H/4-K)^2, after clearing 16/5.
assert (20*S**2 - 4*H*(K+H)**2 - H*(H-4*K)**2).substitute_q(q_in_s).reduce(1,6,rel_s) == 0


def ep_add(p, P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x, y = P
    X, Y = Q
    if x == X and (y+Y) % p == 0:
        return None
    slope = ((Y-y)*pow(X-x, -1, p) if x != X
             else (3*x*x-4*x-3)*pow(2*y, -1,p)) % p
    z = (slope*slope+2-x-X) % p
    return z, (slope*(x-z)-y) % p


def ep_mul(p,n,P):
    su = None
    while n:
        if n & 1:
            su = ep_add(p,su,P)
        P = ep_add(p,P,P)
        n //= 2
    return su


def control(p, pin=None):
    assert p % 5 == 2  # Phi5 is irreducible and this is the designated d=2.
    roots = {}
    for y in range(p):
        roots.setdefault(y*y % p, []).append(y)
    pts = [(x,y) for x in range(p) for y in roots.get((x**3-2*x*x-3*x)%p, [])]
    P = pin if pin is not None else next(P for P in pts if ep_mul(p,5,P) is None)
    assert P in pts and ep_mul(p,5,P) is None
    Q = ep_add(p,P,P)
    assert Q is not None and ep_add(p,Q,Q) == (P[0], -P[1]%p)
    x1,y1=P
    x2,y2=Q
    s=(x1+x2)%p
    q=(x1*x2)%p
    h=(x1-x2)%p
    H=h*h%p
    S=(s**3-3*s*q-2*(s*s-2*q)-3*s)%p
    k=(s*s-q-2*s-3)%p
    assert (s**6-8*s**5-60*s**4-720*s*s+1152*s-576)%p==0
    assert q == (s**3+6*s)*pow(6*s-8,-1,p)%p
    assert (y1*y1+y2*y2)%p==S and (y1*y1-y2*y2)%p==k*h%p
    assert (4*y1*y2-h**3)%p==0

    def const(x):
        return (x%p, 0, 0, 0)

    def add(a,b):
        return tuple((x+y)%p for x,y in zip(a,b))

    def scale(c,a):
        return tuple(c*x%p for x in a)

    def mul(a,b):
        t=[0]*7
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                t[i+j]+=x*y
        for i in range(6,3,-1):
            for j in range(4):
                t[i-4+j]-=t[i]
        return tuple(x%p for x in t[:4])

    def power(a,m):
        r=const(1)
        while m:
            if m&1:
                r=mul(r,a)
            a=mul(a,a)
            m//=2
        return r

    zeta=(0,1,0,0)
    z2,z3,z4=(power(zeta,i) for i in (2,3,4))
    assert power(zeta,5)==const(1)
    root5=add(add(zeta,z4),scale(-1,add(z2,z3)))
    assert mul(root5,root5)==const(5)
    w,w2=add(zeta,scale(-1,z4)), add(z2,scale(-1,z3))
    eta=scale(h,root5)
    r=add(scale(y1,w),scale(y2,w2))
    assert any(r)
    alpha=scale(-pow(2,-1,p),add(const(5*S),scale(k+H,eta)))
    sigma_r=add(scale(y1,w2),scale(-y2,w))
    assert power(r,p)==sigma_r and power(sigma_r,p)==scale(-1,r)
    assert power(eta,p)==scale(-1,eta)
    assert mul(r,r)==alpha
    product=scale(H*pow(4,-1,p)-k,eta)
    assert mul(r,sigma_r)==product
    assert mul(alpha,power(alpha,p))==mul(product,product)
    return {"p":p,"curve_order":len(pts)+1,"P":P,"2P":Q,"s":s,"q":q,
            "H":H,"S":S,"k":k,"eta":eta,"r":r,"sigma_r":sigma_r,
            "alpha":alpha,"r_times_sigma_r":product}


print(json.dumps({
    "sextic_coefficients_ascending":[-576,1152,-720,0,-60,-8,1],
    "q_numerator_coefficients_ascending":[3888,-6960,-360,-620,-60,9],
    "q_denominator":2800,
    "symbolic_remainder_and_norm_checks":True,
    "basis":["1","zeta","zeta^2","zeta^3"],
    "frobenius_controls":[control(127,(87,22)),control(157)],
    "actual_selected_n_or_class_bound_computed":False
},indent=2))
