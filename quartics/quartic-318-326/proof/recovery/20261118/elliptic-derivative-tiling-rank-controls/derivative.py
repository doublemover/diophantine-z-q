"""Rigorous FLINT/Arb interval for L'(E_d,1), positive squarefree d=11 mod12.
Python-flint 0.9.0; no elliptic-curve rank routine. CLI: python derivative.py d [T].
The transcript supplies elementary prime factorizations, or FLINT tests primality of factors.
"""
from sys import argv
from math import prod
from flint import arb, ctx, fmpz, fmpz_poly
import json

def euler(delta, N):
    z = [0] * N
    z[0] = 1
    k = 1
    while delta*k*(3*k-1)//2 < N:
        for j in (delta*k*(3*k-1)//2, delta*k*(3*k+1)//2):
            if j < N: z[j] = (-1)**k
        k += 1
    return fmpz_poly(z)

def certify(d, T, bits=96):
    assert d>0 and d%12==11 and T>=1
    factors = fmpz(d).factor()
    assert all(p.is_prime() and e==1 for p,e in factors)
    assert prod(int(p) for p,e in factors)==d
    ctx.prec = bits
    K = (T+1)//2 # count odd m in [1,T]
    a = euler(1,K).mul_low(euler(2,K),K)
    a = a.mul_low(euler(3,K),K).mul_low(euler(6,K),K)
    c = arb.pi()/(2*arb(3).sqrt()*d)
    partial = arb(0)
    n = fmpz(d)
    for k in range(K):
        m = 2*k+1
        v = a[k]
        if v:
            # a[0] gives q^1. The signed character on odd m is (d/m).
            h = int(n.jacobi(m))
            if h: partial += (2*int(v)*h*arb(1)/m)*(c*m).expint(1)
    t = c*(T+1)
    err = 4*(-t).exp()/(t*(-(-c).expm1()))
    enclosure = partial + ((-err).union(err))
    return dict(d=d,prime_factors=[int(p) for p,e in factors],T=T,precision=bits,
                truncated=str(partial),absolute_tail_upper=str(err.upper()),
                derivative_lower=str(enclosure.lower()),derivative_upper=str(enclosure.upper()),
                nonzero=bool(enclosure>0 or enclosure<0))
if __name__ == '__main__':
    d = int(argv[1]); T = int(argv[2]) if len(argv)>2 else 16*d
    print(json.dumps(certify(d,T),indent=2))
