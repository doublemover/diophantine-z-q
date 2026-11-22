"""Exact normalization canaries; no selected geometric point is instantiated."""
from itertools import product
import json

def eye():
    return ((1, 0), (0, 1))

def mm(a, b, n):
    return tuple(tuple(sum(a[i][h] * b[h][j] for h in range(2)) % n for j in range(2)) for i in range(2))

def tr(a):
    return tuple(zip(*a))

def det(a, n):
    return (a[0][0] * a[1][1] - a[0][1] * a[1][0]) % n

def inv(a, n):
    d = pow(det(a, n), -1, n)
    return ((a[1][1]*d % n, -a[0][1]*d % n), (-a[1][0]*d % n, a[0][0]*d % n))

def rankmod(a, p):
    return 2 if det(a, p) else int(any(x % p for row in a for x in row))

def du(a, b, n):
    return (a[0]*b[0] % n, (a[0]*b[1]+a[1]*b[0]) % n)

def unit(x, n):
    return (1, x % n)

rows = []
for p, support in [(13, (1, 1)), (5, (1, 5)), (5, (5, 1))]:
    prime_square = p*p
    P = ((2, 1), (3, 2))
    U = ((1, 2), (1, 3))
    V = ((3, 2), (1, 1))
    rank = 2 if p == 13 else 1
    runs = 0
    for r in range(1, prime_square):
        if r % p == 0:
            continue
        C = ((r*support[0] % prime_square, 0), (0, r*support[1] % prime_square))
        pol = mm(tr(inv(P, prime_square)), C, prime_square)
        assert mm(tr(P), pol, prime_square) == C
        P1 = mm(mm(inv(U, prime_square), P, prime_square), V, prime_square)
        C1 = mm(mm(tr(V), C, prime_square), U, prime_square)
        pol1 = mm(tr(inv(P1, prime_square)), C1, prime_square)
        assert pol1 == mm(mm(tr(U), pol, prime_square), U, prime_square)
        assert rankmod(pol, p) == rank == rankmod(pol1, p)
        if p == 5:
            assert det(pol, prime_square) % p == 0 and det(pol, prime_square) != 0
            assert sum(any(pol[i][j] % p for i in range(2)) for j in range(2)) == 1
        else:
            assert det(pol, prime_square) % p
        runs += 1
    rows.append(dict(p=p, adapted_unpolarized_generator=support, rank_after_reduction=rank, unit_scalar_cases=runs))

gauges = {}
for p in (5, 13):
    cases = 0
    for a, b, c in product(range(p), repeat=3):
        assert du(du(unit(b,p), unit(c,p),p), unit(-a,p),p) == unit(c+(b-a),p)
        assert (du(unit(a,p), unit(b,p),p) == unit(c,p)) == ((a+b-c) % p == 0)
        cases += 1
    for x in range(p*p):
        red = lambda y: (y[0] % p, y[1] % p)
        assert red(unit(x, p*p)) == unit(x,p)
        assert du(unit(x,p*p), unit(-x,p*p), p*p) == (1,0)
    gauges[p] = dict(triples=cases, unit_restriction_and_inverse=p*p)
print(json.dumps(dict(normalization_only=True, frame_transport=rows, principal_units=gauges), indent=2, sort_keys=True))
