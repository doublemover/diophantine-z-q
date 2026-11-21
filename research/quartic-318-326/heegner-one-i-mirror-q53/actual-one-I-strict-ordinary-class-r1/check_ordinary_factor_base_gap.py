#!/usr/bin/env python3
"""Integer-only comparison of the conditional factor base size and actual test prime."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,json
H=Path(__file__).resolve().parent
def donor(path,sha):
    raw=(H.parent/path).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==sha
    return json.loads(raw)
j=donor('actual-one-I-explicit-line-field-r2/ACTUAL-FIELD-DISCRIMINANTS.json',
        'b9573239c447acd8f6e3d52d412e3041f9a2a19dd50496b2c58ee45afac68e84')
q=donor('actual-one-I-mirror-ray-class-r1/EXACT-ACTUAL-MIRROR-53-PRIME.json',
        'a0870144f7cdb7d84a1e0f4a1c9e19cd7afc69ca2f5ff81a295341eeff35dc7d')
bit=j['point_field_discriminant_bits'];assert bit==8772
x=F(694,1000)
assert sum(x**k/factorial(k) for k in range(7))>2 # log 2 < x
b=F(401,100)*(bit*x)**2
cap=(b.numerator+b.denominator-1)//b.denominator
assert cap<149_000_000
assert all(n%13!=1 or any(n%d==0 for d in range(2,n)) for n in range(2,53))
assert q['norm_of_mirror_test_prime']==53**13
assert 53**13//cap>10**14
print(json.dumps(dict(ell_first_possible_transvection=53,actual_test_prime_norm=53**13,
        same_mirror_discriminant_bits=bit,conditional_GRH_Grenie_Molteni_factor_base_ceiling=cap,
        floor_actual_test_prime_over_conditional_ceiling=53**13//cap,
        unconditional_standard_Minkowski_factor_base_decimal_digits=j['minkowski_standard_bound_decimal_digits']),
    sort_keys=True,indent=2))
