"""Independent Jacobian-coordinate verifier. No affine producer imports, no oracle."""
from copy import deepcopy
from itertools import product
from pathlib import Path
from math import gcd, isqrt, lcm, prod
import json


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def multiply(p, a, point, n):
    """Jacobian double/add formulas, (X:Y:Z) represents (X/Z^2,Y/Z^3)."""
    infinity = (1, 1, 0)
    def double(P):
        X, Y, Z = P
        if Z == 0 or Y == 0:
            return infinity
        S = 4*X*Y*Y % p
        M = (3*X*X+a*pow(Z, 4, p)) % p
        T = (M*M-2*S) % p
        return T, (M*(S-T)-8*pow(Y, 4, p)) % p, 2*Y*Z % p
    def add(P, Q):
        X1, Y1, Z1 = P
        X2, Y2, Z2 = Q
        if Z1 == 0:
            return Q
        if Z2 == 0:
            return P
        U1, U2 = X1*Z2*Z2 % p, X2*Z1*Z1 % p
        S1, S2 = Y1*pow(Z2, 3, p) % p, Y2*pow(Z1, 3, p) % p
        H, R = (U2-U1) % p, (S2-S1) % p
        if H == 0:
            return double(P) if R == 0 else infinity
        X3 = (R*R-H**3-2*U1*H*H) % p
        Y3 = (R*(U1*H*H-X3)-S1*H**3) % p
        return X3, Y3, H*Z1*Z2 % p
    out = infinity
    current = (*point, 1)
    while n:
        if n % 2:
            out = add(out, current)
        current = double(current)
        n //= 2
    X, Y, Z = out
    if Z == 0:
        return None
    iz = pow(Z, -1, p)
    return [X*iz*iz % p, Y*iz**3 % p]


def verify(data):
    assert [row['prime'] for row in data['rows']] == [9649, 95441, 387089, 1473041]
    pairs = []
    for row in data['rows']:
        p = row['prime']
        assert is_prime(p) and p > 3
        assert len(row['sides']) == 2
        assert sum(s['sqrt_two'] for s in row['sides']) == p
        orders = []
        for side in row['sides']:
            r, a, P, n = side['sqrt_two'], side['curve_a4'], side['point'], side['order']
            assert 0 < r < p and r*r % p == 2
            assert a == -(3-r)**2 % p
            assert P == [(1+r) % p, 2*r % p]
            x, y = P
            assert (y*y-x*x*x-a*x) % p == 0
            assert (-64*a**3) % p != 0  # nonsingular short Weierstrass model
            factors = {int(q): e for q, e in side['factorization'].items()}
            assert n > 1 and prod(q**e for q, e in factors.items()) == n
            assert factors and all(is_prime(q) and e >= 1 for q, e in factors.items())
            assert set(side['prime_drops']) == {str(q) for q in factors}
            assert multiply(p, a, P, n) is None and side['annihilation'] is None
            for q in factors:
                Q = multiply(p, a, P, n//q)
                assert Q is not None and Q == side['prime_drops'][str(q)]
                assert (Q[1]**2-Q[0]**3-a*Q[0]) % p == 0
            orders.append(n)
        pairs.append(orders)
    Pi = prod(row['prime'] for row in data['rows'])
    assert Pi == data['independent_prime_product']
    for scenario in data['four_position_scenarios']:
        L, h0 = scenario['L'], scenario['h0']
        actual = {tuple(c['orientation_bits']) for c in scenario['candidates']}
        expected = set()
        for bits in product((0, 1), repeat=4):
            M = lcm(*(row[bit] for row, bit in zip(pairs, bits)))
            N = lcm(*(row[1-bit] for row, bit in zip(pairs, bits)))
            A = Pi**3*M
            if gcd(A, N) == 1 and h0 % gcd(A, L) == 0 and (h0-1) % gcd(N, L) == 0:
                expected.add(bits)
        assert actual == expected and len(actual) == scenario['orientation_count'] == len(scenario['candidates'])
        for c in scenario['candidates']:
            bits = c['orientation_bits']
            M = lcm(*(row[bit] for row, bit in zip(pairs, bits)))
            N = lcm(*(row[1-bit] for row, bit in zip(pairs, bits)))
            assert c['minus'] == M and c['plus'] == N
            assert c['period'] == lcm(Pi**3*M, N, L)
            assert 0 <= c['h'] < c['period']
            assert c['h'] % (Pi**3*M) == 0 and (c['h']-1) % N == 0 and (c['h']-h0) % L == 0


def main():
    data = json.loads(Path(__file__).with_name('REDUCTION-CERTIFICATES.json').read_text())
    verify(data)
    mutations = []
    bad = deepcopy(data); bad['rows'][0]['prime'] += 2; mutations.append(bad)
    bad = deepcopy(data); bad['rows'][0]['sides'][0]['sqrt_two'] += 1; mutations.append(bad)
    bad = deepcopy(data); bad['rows'][0]['sides'][0]['point'][0] += 1; mutations.append(bad)
    bad = deepcopy(data); bad['rows'][0]['sides'][0]['order'] *= 2; mutations.append(bad)
    bad = deepcopy(data); bad['rows'][0]['sides'][0]['factorization']['149'] = 2; mutations.append(bad)
    bad = deepcopy(data); bad['rows'][0]['sides'][0]['prime_drops']['149'][0] += 1; mutations.append(bad)
    bad = deepcopy(data); bad['four_position_scenarios'][0]['candidates'].pop(); mutations.append(bad)
    bad = deepcopy(data); bad['four_position_scenarios'][0]['candidates'][0]['h'] += 1; mutations.append(bad)
    for bad in mutations:
        try:
            verify(bad)
        except AssertionError:
            pass
        else:
            raise AssertionError('corrupted certificate accepted')
    print(json.dumps({'prime_fields_checked': 4, 'literal_R_orders_checked': 8,
        'independent_algorithm': 'Jacobian projective arithmetic, distinct from affine producer',
        'mutation_controls_rejected': len(mutations),
        'opposite_orders_refined': [149, 2986, 24116, 92212],
        'native_Lean_quotient_order_acceptance': False,
        'original_fifteen_position_Values': False}, indent=2))

if __name__ == '__main__':
    main()
