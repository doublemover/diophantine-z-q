"""Exact rational coefficient expansion and integer residue proof."""
from fractions import Fraction as F
from math import prod
import json

raw = (
    F(4376874610839020), F(101783690143177584),
    F(267108917866935984 + 533801448346128768),
    533801448346128768 * F(496408687, 100291113),
    533801448346128768 * F(197130368, 33430371),
)
factors = [(7446, 661), (7446, 1861), (29784, 7445), (476544, 119479)]
a = [4]
for slope, shift in factors:
    b = [0] * (len(a) + 1)
    for i, x in enumerate(a):
        b[i] += shift * x
        b[i + 1] += slope * x
    a = b
assert tuple(a) == raw
assert all(p.denominator == 1 for p in raw)
assert 17 * 114444 * 4 == 204**2 * 187

res = {}
for m in (3, 8, 17, 24):
    xs = sorted({(u * (u + 1)) % m for u in range(m)})
    rr = [[x, prod(s * x + c for s, c in factors) % m] for x in xs]
    res[m] = rr
assert {r for x, r in res[24]} == {11}
assert {r for x, r in res[17]} == {14}
assert 187 * 11 % 24 == 17

assert prod(c for s, c in factors) * 187 == 204618888056724185
print(json.dumps({'ascending_R_coefficients': a, 'ascending_x_class_residues_R_div_4': res,
                  'constant_17_times_114444_times_4': 17 * 114444 * 4,
                  'scalar_mark_squareclass_factor': 187,
                  'literal_zero_input_positive_integer_representative': 204618888056724185,
                  'scope': 'exact coefficients and residues for every integer input, not an analytic rank test'},
                 indent=2, sort_keys=True))
