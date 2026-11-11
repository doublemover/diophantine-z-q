#!/usr/bin/env python3
"""Finite regression only. Does not compile Lean or prove an asymptotic."""
import cmath
import itertools
import json
import math

points = list(itertools.product(range(-1, 2), repeat=5))
def quadric(k, x):
    a, b, c, d, w = x
    return a*a + b*b - c*c - d*d - k*w*w
def weight(x):
    return complex(1 + sum(t*t for t in x), sum(x)/7)
def phase(t):
    return cmath.exp(2j*math.pi*t)

checked = 0
for k, q, a, beta in itertools.product((318, 326), (1, 2, 3, 4), (-2, 0, 1), (0, 1/8, math.sqrt(2)/10)):
    residues = list(itertools.product(range(q), repeat=5))
    assert len(residues) == q**5
    fibers = {r: [] for r in residues}
    for x in points:
        r = tuple(t % q for t in x)
        assert (quadric(k, x)-quadric(k, r)) % q == 0
        fibers[r].append(x)
    assert sum(map(len, fibers.values())) == len(points)
    left = sum(weight(x)*phase((a/q+beta)*quadric(k,x)) for x in points)
    right = sum(phase(a*quadric(k,r)/q)*sum(weight(x)*phase(beta*quadric(k,x))
                for x in fibers[r]) for r in residues)
    assert abs(left-right) < 1e-8, (k,q,a,beta,left,right)
    checked += 1
print(json.dumps({'finite_rational_arc_cases': checked, 'points_per_case': len(points),
  'moduli': [1,2,3,4], 'primitive_numerators_required': False,
  'complex_phase_tolerance': 1e-8, 'scope': 'finite numerical and integer regression only',
  'local_lean': 'NOT_RUN', 'global_asymptotic': 'NOT_CLAIMED'}, indent=2))
