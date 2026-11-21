"""Exact unit phase and normalization checks; no Hasse theorem is tested by finite sampling."""
from fractions import Fraction
from itertools import product
import json

result = {}
for p in (5, 7, 11, 13):
    row = {}
    squares = {i*i % p for i in range(1, p)}
    for u, v in product(sorted(set(range(1, p))-squares), repeat=2):
        candidates = [
            (z, y) for z in range(1, p) for y in range(p)
            if (y*y-u*(z*z-v)*(z*z+3*v)) % p == 0
        ]
        if p == 5:
            candidates = [(z, y) for z, y in candidates if y == 0 and (z*z+3*v) % p == 0]
            assert all((2*z*u*(z*z-v)) % p for z, _ in candidates)
        if p == 7:
            candidates = [(z, y) for z, y in candidates if y and (z*z-3*v) % p == 0]
        assert candidates
        row[f"{u},{v}"] = min(candidates)
    result[str(p)] = row

# Check the actual change of variables on rational scalars, including negative
# valuation (b=1/7²); these are polynomial identities, not rational witnesses.
for b,t,z,gamma in product((Fraction(1,49), Fraction(16,9), Fraction(25,17)),
    (Fraction(1),Fraction(10,7)),(Fraction(3,5),Fraction(-2)),
    (Fraction(1,343),Fraction(7))):
    B = 17*b
    V = B**2*(1-b/17)
    beta = Fraction(1,7)
    u = B / beta**2
    v = V / gamma**2
    P = B*t
    s = gamma*z
    rhs1 = B*(B-P)*(B+3*P)
    rhs2 = B*s*s*(B*s*s-P*V)*(B*s*s+3*P*V)
    assert rhs1 == B**2 * B*(1-t)*(1+3*t)
    assert rhs2 == (B*beta*gamma**3*z)**2 * u*(z*z-t*v)*(z*z+3*t*v)
print(json.dumps(result, indent=2, sort_keys=True))
