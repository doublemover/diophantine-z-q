#!/usr/bin/env python3
from fractions import Fraction as Q
from math import gcd, isqrt, prod
import json

def crt(eqns):
    a, m = 0, 1
    for v, r in eqns:
        assert gcd(m, v) == 1
        a += m * (((r - a) * pow(m, -1, v)) % v)
        m *= v
    assert 0 <= a < m and all(a%v == r%v for v,r in eqns)
    return a, m

def small_divisor(n):
    assert n > 1
    if n%2 == 0:
        return 2 if n != 2 else None
    return next((i for i in range(3, isqrt(n)+1, 2) if n%i == 0), None)

def first_prime(a, m):
    rows = []
    while (d := small_divisor(a)):
        rows.append([a, d])
        a += m
    return a, rows

def main():
    a0 = 2*11*37*2399
    assert all(small_divisor(p) is None for p in (3,5,7,11,17,29,37,103,241,2399))
    # Gaussian odd norm, mod 32 and mod 7; fixed old 1 mod 408.
    old_a, old_m = crt([(32,17),(7,3),(3,1),(17,1)])
    assert (old_a, old_m) == (8977, 11424)
    assert old_a % 408 == 1
    fixed = [(old_m, old_a),(5,1),(29,1),(103,1)]
    pa, pm = crt(fixed+[(241,1)])
    qa, qm = crt(fixed+[(241,17)])
    assert pm == qm and (pa,qa,pm) == (14685286801,29699621521,41118803040)
    p0, badp = first_prime(pa,pm)
    q0, badq = first_prime(qa,qm)
    assert (p0,q0) == (96922892881,70818424561)
    gm = 16*3*5*7*11*17*29*37*103*241*2399
    assert gm == 20074055728317360
    roots = list(map(Q, ("0","-1/2","-1","1/2399","-32/407")))
    R = max(roots)
    # Note q0 below is the source order-only prime floor, not the fixed Selmer prime 103.
    def bounds(aq):
        nums = [p0+(aq**2)*q0*(R-r) for r in roots if r != R]
        assert all(n.denominator == 1 for n in nums)
        g = q0*p0*prod(n.numerator for n in nums)
        return {"AQ":aq, "offset_contacts":[n.numerator for n in nums],
                "d_lower":g, "D_lower":17*103*g}
    exact, relaxed = bounds(a0*gm), bounds(gm//2)
    assert exact["D_lower"] > 278*10**242
    assert relaxed["D_lower"] > 10**191
    # Tatuzawa with eps=1/540, pi<22/7, strict h(D)>10^118.
    assert 244*9 > 540*4 # log(10)>9/4 implies exact k>exp(540).
    B_num, B_den = 655*7,1000*540*22
    assert (B_num**540)*(exact["D_lower"]**269) > (10**118*B_den)**540
    # Independently check the anchored row190 threshold, without expanding a point.
    anchor_floor = (3**32767-1)**2-8
    assert anchor_floor > 2**103860
    print(json.dumps({"m_gauss_divisor":gm,"old_rational_progression":[old_a,old_m],
                      "contact":[pa,p0,badp],"source_q":[qa,q0,badq],
                      "rational_modulus":pm,"protected":exact,"relaxed":relaxed,
                      "class_number_floor":"10^118","ring_orbit_factor":242,
                      "anchored_row190_log2_lower":"2^103860","slope_clearing_divisor":a0},
                     indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
