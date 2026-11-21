import itertools
import json
from math import isqrt


def symbol(a, p):
    return {0: 0, 1: 1, p - 1: -1}[pow(a % p, (p - 1) // 2, p)]


def mul(a, b, p):
    return tuple(sum(a[i * 2 + k] * b[k * 2 + j] for k in range(2)) % p
                 for i in range(2) for j in range(2))


def det(a):
    return a[0] * a[3] - a[1] * a[2]


def inverse(a, p):
    b = pow(det(a) % p, -1, p)
    return tuple(x * b % p for x in (a[3], -a[1], -a[2], a[0]))


def e_set(v, p):
    values = set()
    for x, y in itertools.product(range(p), repeat=2):
        n, m = (v[0] * x + v[1] * y) % p, (v[2] * x + v[3] * y) % p
        if n or m:
            c = symbol(x * m - y * n, p)
            assert c
            values.add(c)
    assert len(values) == 1
    return values.pop()


def e_small(u, p):
    for w in [(1, 0), (0, 1)]:
        x, y = w
        c = symbol(x * (u[2]*x + u[3]*y) - y * (u[0]*x + u[1]*y), p)
        if c:
            return c
    raise AssertionError(u)


p, h, r = 415721, 2207, 976393
N = 205042530
assert all(n % d for n in (p, h) for d in range(2, isqrt(n) + 1) if d <= isqrt(n))
assert N == 210 * r and r == 11 * 37 * 2399 and symbol(-h, p) == 1

mats = list(itertools.product(range(3), repeat=4))
gl = [g for g in mats if det(g) % 3]
nils = [v for v in mats if any(v) and mul(v, v, 3) == (0, 0, 0, 0)]
for u in nils:
    e = e_set(u, 3)
    for g in gl:
        v = mul(mul(g, u, 3), inverse(g, 3), 3)
        assert e_set(v, 3) == symbol(det(g), 3) * e
u = (0, 0, 1, 0)
g = (2, 1, 1, 1)
nonsquare = next(n for n in range(2, h) if symbol(n, h) == -1)
g2 = (nonsquare, 0, 1, 1)
h_probes = []
for mat in (g, g2):
    a = e_small(u, h)
    b = e_small(mul(mul(mat, u, h), inverse(mat, h), h), h)
    assert symbol(det(mat), h) * a == b
    h_probes.append([list(mat), det(mat), a, b])

# Literal reduced CM15 two-term normalization from the separately
# proved whole trace, not a new embedding enumeration.
def plus(v, w):
    return tuple((a + b) % 5 for a, b in zip(v, w))


def scale(a, v):
    return tuple(a * x % 5 for x in v)


def multiply(v, w):
    a, b = v
    c, d = w
    return ((a*c+2*b*d) % 5, (a*d+b*c) % 5)


def frob(v):
    return (v[0], -v[1] % 5)


rho = (0, 1)
c = (1, 2)
c2 = frob(c)
tau = scale(pow(-3, -1, 5), rho)
d_A = [scale(pow(2, -1, 5), multiply(tau, ci)) for ci in (c, c2)]
assert d_A == [(1, 4), (4, 4)] # 1-rho, -1-rho, exact in both frames.
F = pow(4, -1, 5)
weights = [scale(F, c), scale(-F, c2)]
s = plus(*weights)
assert s == rho and frob(s) == scale(-1, s)


def anti_coordinate(v):
    a, b = scale(pow(2, -1, 5), plus(v, scale(-1, frob(v))))
    assert a == 0
    return b


coords = [anti_coordinate(v) for v in weights]
assert coords == [3, 3] and sum(coords) % 5 == 1
jet = multiply(scale(4, tau), s)
assert jet == (4, 0) and symbol(2, 3) == -1
print(json.dumps(dict(
    production_constants=dict(p=p, h=h, r=r, N=N, psi_Pp=symbol(-h, p)),
    complete_h3_nilpotents=len(nils), complete_h3_frames=len(gl),
    h2207_frame_law_controls=h_probes,
    ramified_CM15_p5=dict(c1=c, c2=c2, derivatives_A=d_A,
                          relative_genus_sign=symbol(2, 3), weights=weights,
                          signed_before_common_factor=s,
                          anti_iso_projected=coords, exact_fourfold_jet=jet)),
    indent=2))
