"""Check the exact historical p_a cell against the repaired h; no search."""
from fractions import Fraction
from hashlib import sha256
from math import prod
from pathlib import Path
import json
import sys


def exact(path, digest):
    raw = Path(path).read_bytes()
    assert sha256(raw).hexdigest() == digest
    return json.loads(raw)


repair = exact(sys.argv[1], 'f5dbe608ef26c9bde7a3ff31f40770ba9924fd4e9071e49520761ac3f39e7b64')
inherited = exact(sys.argv[2], '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
p = 415721
pp = p * p
h = int(repair['final_h'])
assert int(repair['literal_J']) == int(inherited['literal_scalar_J'])
assert h % int(inherited['simultaneous_h_modulus']) == int(inherited['simultaneous_h_residue'])
a = repair['a']
b = repair['b']
assert a % p == 0 and a % pp != 0 and b % p != 0
old, = [r for r in inherited['rows'] if r['prime'] == p]
cell, = [r for r in repair['old_cells_W_a_unit_b_unit'] if r[0] == p]
W = cell[1]
scales = old['scales_mod_p2']
ord1, ord2 = [r['order'] for r in old['arms']]
z0 = [r['formal_first_z'][0] for r in old['arms']]
assert all(z % p == 0 and z % pp != 0 for z in z0)
assert (ord1, ord2) == (103693, 29)
assert (h % ord1, h % ord2, h % p**4) == (0, 1, p**3)
assert old['assigned_scale'] == 1 and old['assigned_root_index'] == 4
roots = [Fraction(0), Fraction(-1, 2), Fraction(-1), Fraction(-32, 407), Fraction(1, 2399)]


def red(q, mod):
    return q.numerator * pow(q.denominator, -1, mod) % mod


assert len({red(q, p) for q in roots}) == 5
ratios = [c * pow(scales[1], -1, pp) % pp for c in scales]
assert (W * pow(scales[1], -1, pp)) % pp == old['r_over_d_mod_p2']
T = [pow(r * W, 2, pp) for r in ratios]
f = [prod(t - red(r, pp) for r in roots) % pp for t in T]
s = roots[3]
assert (T[1] - red(s, pp)) % pp == p
assert f[1] == 285703 * p and f[0] % p != 0 and f[2] % p != 0
assert all((t - 1) % p != 0 for t in T)
print(json.dumps(dict(prime=p, W_p2=W, stripped_a=a//p, b_p=b%p,
    T_rows_p2=T, F_rows_p2=f, middle_stripped_F=f[1]//p,
    middle_delta_mod_p=(T[1]-1)%p, h_moduli=[ord1,ord2,p**4],
    h_residues=[h%ord1,h%ord2,h%p**4],first_formal_returns_mod_p2=z0), indent=2))
