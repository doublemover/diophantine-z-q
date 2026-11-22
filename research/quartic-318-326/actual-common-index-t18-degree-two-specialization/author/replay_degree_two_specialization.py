#!/usr/bin/env python3
"""Arithmetic control for the degree-two secant family, not an actual common index."""
from fractions import Fraction as F
from math import prod, isqrt
import json

beta = 204618888056724185
ls = 114444 * 4376874610839020
ps = [5, 11, 17, 163, 661, 733, 1489, 1861]
assert all(all(p % j for j in range(2, isqrt(p) + 1)) for p in ps)
assert beta == prod(ps) and 17 * ls == 204**2 * beta
t = 18
A = 1 + 3 * beta * t*t
k = (1 - beta * t*t) * (1 - 9 * beta * t*t)
n = beta * k
u = beta * A*A
a = F(8 * beta * t * (1 - 3 * beta * t*t), A)
B0 = F(12 * n*n, u)
assert B0 == 3*beta * F(2*k,A)**2

def vp(x,p):
    x = F(x)
    def order(y):
        assert y
        e = 0
        while y % p == 0:
            y //= p
            e += 1
        return e
    return order(x.numerator) - order(x.denominator)

rows = []
for p in [2, 3] + ps:
    vc = vp(F(12,1+ls),p)  # W unit; this does not use its numerical value
    va, vA, vB = (vp(x,p) for x in (a,A,B0))
    u_depth, v_depth = vp(2,p)+va+vc, vp(2,p)+vA
    assert u_depth > v_depth
    relative = vB + 2*vc - 2*v_depth
    assert relative >= (3 if p == 2 else 1)
    rows.append([p,vc,va,vA,vB,v_depth,relative])
assert [r[-1] for r in rows] == [4,3]+[1]*8

def pair(x):
    return [x.numerator,x.denominator]

controls=[]
for q in (F(10**47), F(10**47+1)):
    w=(q+B0/q)/2
    m=(q-B0/q)/2-a
    c=2*A/(m-a)
    z=(m-a)*w
    delta=1-beta*c*c
    assert 0<c and 0<delta<1 and z
    assert c == 4*A*q/(q*q-4*a*q-B0)
    assert w*w == (m+a)**2+B0
    assert ((m-a)**2-4*beta*A*A)*((m+a)**2+B0) == delta*z*z
    assert (w*c)**2 == (2*a*c+2*A)**2+B0*c*c
    assert q == w+m+a
    controls.append({"q": pair(q), "c": pair(c)})
assert controls[0]["c"] != controls[1]["c"]
print(json.dumps({"beta": beta, "t": t,
                  "depth_rows_p_c_a_A_B0_centre_relative":rows,
                  "degree_two_controls":controls,
                  "actual_index_or_companion_evaluated":False},indent=2))
