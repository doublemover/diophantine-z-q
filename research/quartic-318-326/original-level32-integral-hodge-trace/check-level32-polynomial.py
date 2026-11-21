"""Independent exact checks of the level-32 polynomial and q normalization."""
from math import comb
import sympy as s

U, J, X, V = s.symbols("U J X V")
Ah = U**4 + 240*U**3 + 2144*U**2 + 3840*U + 256
Dh = U*(4-U)**8*(4+U)**2
A = X**4 + 60*X**3 + 134*X**2 + 60*X + 1
D = X*(1-X)**8*(1+X)**2
alt = 16*(1+14*V+V**2)**3/(V*(1-V)**4)
assert s.cancel(alt.subs(V,4*X/(1+X)**2) - 4*A**3/D) == 0
assert s.cancel((Ah**3/Dh).subs(U,4*X) - 4*A**3/D) == 0
P = s.Poly(Ah**3-J*Dh, U, J)
assert s.Poly(P.as_expr(),U).degree() == 12
assert s.Poly(P.as_expr(),U).LC() == 1
checks = [(0,24,1),(4,48,8),(-4,36,2)]
weighted = 0
for a,k,power in checks:
    value = P.as_expr().subs(U,a)
    assert s.expand(value) == 2**k
    Q, r = s.div(P.as_expr()-value,U-a,U)
    assert r == 0
    assert s.Poly(Q,U,J,domain=s.ZZ)
    weighted += k*power
assert weighted==480
assert s.cancel(Dh*s.diff(Ah**3/Dh,U)-s.diff(P.as_expr(),U).subs(J,Ah**3/Dh))==0

PREC = 32
def const(c):
    return [c] + [0]*PREC
def add(a,b):
    return [x+y for x,y in zip(a,b)]
def scale(c,a):
    return [c*x for x in a]
def mul(a,b):
    r = const(0)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:PREC+1-i]):
                r[i+j] += x*y
    return r
def pow_(a,n):
    r = const(1)
    while n:
        if n % 2:
            r = mul(r,a)
        a = mul(a,a)
        n //= 2
    return r
def prod(d,exponent):
    r = const(1)
    for j in range(d,PREC+1,d):
        f = const(0)
        for k in range(PREC//j+1):
            if exponent >= 0 and k <= exponent:
                f[j*k] = (-1)**k*comb(exponent,k)
            elif exponent < 0:
                f[j*k] = comb(-exponent+k-1,k)
        r = mul(r,f)
    return r
def eval_(coefficients,x):
    r = const(0)
    for c in reversed(coefficients):
        r = add(mul(r,x),const(c))
    return r
q = const(0); q[1] = 1
xs = scale(4,mul(q,mul(prod(2,4),mul(prod(8,8),prod(4,-12)))))
us = scale(4,xs)
ds = mul(us,mul(pow_(add(const(4),scale(-1,us)),8),pow_(add(const(4),us),2)))
As = eval_([256,3840,2144,240,1],us)
E4 = [1] + [240*sum(i**3 for i in range(1,n+1) if n%i == 0) for n in range(1,PREC+1)]
Delta = mul(q,prod(1,24))
assert mul(ds,pow_(E4,3)) == mul(Delta,pow_(As,3))
assert xs[:5] == [0,4,0,-16,0]
print("PASS exact two substitutions and derivative; degree 12 monic; evaluations 2^24,2^48,2^36; integral multiplier 2^480")
print(f"PASS original lattice-parameter J(q), cross-multiplied E4^3/Δ and explicit level-32 polynomial through q^{PREC}")
