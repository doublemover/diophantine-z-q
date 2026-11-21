#!/usr/bin/env python3
"""Exact integer lower envelopes; no CM enumeration or new numerical sources."""
import json
from fractions import Fraction as F
from math import isqrt, lcm, prod

def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))

M = lcm(32, 408, 7)
ray = [r for r in range(M) if r % 32 == 17 and r % 408 == 1 and r % 7 == 3]
assert ray == [8977]
all_ray = [n for n in range(ray[0], 180338, M) if prime(n)]
assert all_ray == [54673, 77521, 123217, 157489, 168913, 180337]
first, second = all_ray[:2]
helpers = [n for n in range(1, 194, 24) if prime(n)]
assert helpers == [73, 97, 193]
q0_floor = 7
D0 = prod([2,11,37,2399])
assert prime(2399)
m0 = prod([16,3,7,11,13,17,19,37,2399])
rho = F(1,2399)
roots = [F(0), -F(1,2), -F(1), -F(32,407)]
assert 11*37 == 407 and all(r < rho for r in roots)
# e < 11/4 and (11/4)^9 < 10^4 imply log(10)>9/4.
assert F(8,3) + F(5,96) < F(11,4) and 11**9 < 4**9 * 10**4

def floor(AQ, epsilon_den, h_lower, h_decade):
    row_floors_f = [first + AQ**2*first*(rho-r) for r in roots]
    assert all(x.denominator == 1 for x in row_floors_f)
    row_floors = [int(x) for x in row_floors_f]
    beta = 17*first*second*prod(row_floors)
    n = beta*q0_floor*prod(helpers)
    assert 2 < epsilon_den and 112 < 10*epsilon_den
    assert n > 10**h_decade and 9*h_decade > 4*epsilon_den
    # h > (131/200)/(epsilon_den*pi) * n^(1/2-1/epsilon_den).
    # Replace pi by its strict upper bound 22/7 and compare integers.
    assert epsilon_den % 2 == 0
    assert (h_lower*200*epsilon_den*22)**epsilon_den < \
           (131*7)**epsilon_den * n**(epsilon_den//2-1)
    b = isqrt(7*n)
    return {
        "mandatory_DQ_over_c": AQ,
        "four_other_prime_floors": row_floors,
        "beta_floor": beta,
        "n_each_floor": n,
        "n_each_digits": len(str(n)),
        "n_each_bits": n.bit_length(),
        "sqrt_floor": isqrt(n),
        "A_at_13_one_mod26_branch_min_candidates": (2*b+1)//26,
        "A_at_19_one_mod38_branch_min_candidates": (2*b+1)//38,
        "Tatuzawa_epsilon_den": epsilon_den,
        "one_of_two_distinct_orbits_strictly_larger_than": h_lower,
    }

assert m0//2 == prod([8,3,7,11,13,17,19,37,2399])
ans = {
    "common_genuine_prime_ray": ray[0],
    "common_ray_modulus": M,
    "first_six_in_weak_ray": all_ray,
    "first_three_helper_primes_1_mod24": helpers,
    "prime_q0_floor": q0_floor,
    "D_over_c_divisibility": D0,
    "protected_base_ray_conductor_divisibility": m0,
    "published_cleared_key": floor(D0*m0,400,8*10**85,179),
    "no_F0_divisibility_but_same_row_ray_and_protected_negative_T": floor(m0//2,280,5*10**59,126),
    "scope": "No numerical prepared detector input, factorization, CM trace, or rank claim.",
}
print(json.dumps(ans, indent=2, sort_keys=True))
