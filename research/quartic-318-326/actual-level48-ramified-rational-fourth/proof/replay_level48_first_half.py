#!/usr/bin/env python3
"""Exact bounded checks: eta divisor, isogeny lift phase, first-half parity."""
from fractions import Fraction
from itertools import product
from math import gcd, prod
import json


def v(n, p):
    assert n
    k = 0
    while n % p == 0:
        k += 1
        n //= p
    return k


def delta_rows():
    r = {2: -1, 4: 2, 6: 3, 8: -3, 12: -2, 24: 1}
    den = [1, 2, 3, 4, 6, 8, 12, 16, 24, 48]
    sums = [sum(r.values()), sum(d*k for d, k in r.items()),
            sum(48//d*k for d, k in r.items())]
    assert sums == [0, 0, 0]
    char = prod(Fraction(d)**k for d, k in r.items())
    assert char == Fraction(9, 16)
    orders = {c: sum(Fraction(48*gcd(c, d)**2*k, 24*gcd(c*c, 48)*d)
                     for d, k in r.items()) for c in den}
    assert {c: x for c, x in orders.items() if x} == {3: 2, 6: 2, 8: -2, 16: -2}
    weights = [sum(k*v(d, p) for d, k in r.items()) for p in (2, 3)]
    assert weights == [-4, 2]
    return {"eta_exponents": r, "newman_sums": sums,
            "square_character_constant": str(char),
            "cusp_orders": {c: int(orders[c]) for c in den},
            "prime_2_3_weight_sums": weights,
            "prime_2_3_f_valuation_connected_etale": [[0, 2], [0, -1]]}


def ec_add(P, Q, a, b, p):
    if P is None:
        return Q
    if Q is None:
        return P
    u, v = P
    U, V = Q
    if u == U and (v+V) % p == 0:
        return None
    lam = ((3*u*u+2*a*u+b) * pow(2*v, -1, p) if u == U else
           (V-v) * pow(U-u, -1, p)) % p
    X = (lam*lam-a-u-U) % p
    return X, (lam*(u-X)-v) % p


def exact_lift_rows():
    rows = {}
    for p in (11, 13, 23, 37, 47, 59, 61, 71, 73):
        pts = [None] + [(u, w) for u in range(p) for w in range(p)
                        if (w*w-u*(u*u-14*u+1)) % p == 0]
        T = (0, 0)

        def add(P, Q):
            return ec_add(P, Q, -14, 1, p)

        def base(P):
            if P in (None, T):
                return None
            u, w = P
            inv = pow(u, -1, p)
            x = (3+w*w*pow(4, -1, p)*inv*inv) % p
            y = (w*(1-inv*inv)*pow(8, -1, p)) % p
            assert (y*y-x*(x+1)*(x-3)) % p == 0
            return x, y

        def R(P):
            if P is None:
                return 1
            if P == T:
                return p-1
            x, _ = base(P)
            if x in (0, p-1):
                return None
            u, _ = P
            return (u-pow(u, -1, p))*pow(4*x, -1, p) % p

        ss = [P for P in pts if base(P) == (3, 0)]
        assert len(ss) == 2 and add(ss[0], T) == ss[1]
        assert all(add(S, S) is None for S in ss)
        n = 0
        for A in pts:
            r = R(A)
            if r is None:
                continue
            Aminus = None if A is None else (A[0], (-A[1]) % p)
            assert R(add(A, T)) == (-r) % p
            for S in ss:
                B = add(S, Aminus)
                assert add(A, B) == S
                assert r*R(B) % p == R(S)
                assert R(S)**2 % p == 4*pow(3, -1, p) % p
                n += 1
        for m in (2, 4, 6, 8):
            for count in range(m+1):
                total = None
                for j in range(m):
                    total = add(total, ss[int(j < count)])
                raw = pow(R(ss[0]), m-count, p)*pow(R(ss[1]), count, p) % p
                assert raw == (R(total)*pow(4*pow(3, -1, p), m//2, p)) % p
        rows[p] = {"E_sharp_points": len(pts), "unit_pair_identities": n,
                   "T3_lifts": ss, "R_values": [R(S) for S in ss]}
    return rows


def root_mod(a, p, d=10):
    r = 1
    for k in range(1, d):
        m = p**k
        candidates = [r+i*m for i in range(p) if ((r+i*m)**2-a) % (p*m) == 0]
        assert len(candidates) == 1
        r = candidates[0]
    return r


def half_rows():
    rows = []
    for p, e in product((5, 7, 17, 29), (-2, -1, 0)):
        roots = [root_mod(1+c*p**(1-2*e), p) for c in (0, -1, 3)]
        for sig in product((-1, 1), repeat=3):
            a, b, c = [s*r for s, r in zip(sig, roots)]
            sums = [v(u+w, p)+e for u, w in ((a, b), (a, c), (b, c))]
            assert sums == [e if sig[i] == sig[j] else 1-e for i, j in
                            ((0, 1), (0, 2), (1, 2))]
            assert (sums[1]+sums[2]) % 2 == (sig[0] != sig[1])
            assert (sums[0]+sums[2]) % 2 == (sig[0] != sig[2])
        rows.append([p, e, 8])
    return rows


print(json.dumps({"modular_unit": delta_rows(), "signed_lift_pairs": exact_lift_rows(),
                  "first_half_parities": half_rows()}, sort_keys=True, indent=2))
