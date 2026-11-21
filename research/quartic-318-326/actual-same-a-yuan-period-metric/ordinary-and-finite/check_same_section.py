#!/usr/bin/env python3
"""Replay the rational equality between actual coefficient formulas.

Uses the literal contacts/gauge but arithmetic samples, not actual QM
closed points or tests of representability/KS.
"""
import json
from fractions import Fraction as Q
from itertools import product
from math import prod

b = (0,32,76832,-343)
c = (-14,-6,42,-21)
J = 2765952000
count, zeros = 0, 0
for t, d, dd, da in product((Q(11,7), Q(-1,4), Q(73), Q(512,3)),
                            range(1,8), (-3,0,13), (-6,0,1,7)):
    a = t*d
    P = prod(t-u for u in b)
    assert P != 0
    pole = prod(a-u*d for u in b)
    assert pole == P*d**4
    diffnum = d*da-a*dd
    direct = Q(J**2*diffnum**2,pole)
    D = Q(da,d) - a*Q(dd,d**2)
    S = (Q(J**2,P),Q(t*J**2,P))
    for k in range(4):
        rho = Q(c[k],4*(t-b[k]))
        ref = tuple(s/rho for s in S)
        assert (direct, t*direct) == tuple(x*rho*D**2 for x in ref)
        zeros += int(D == 0)
        count += 1
print(json.dumps({'contacts': b, 'twists': c, 'J': J, 'pairs':count,
                  'zero_differential_canaries':zeros},indent=2,sort_keys=True))
