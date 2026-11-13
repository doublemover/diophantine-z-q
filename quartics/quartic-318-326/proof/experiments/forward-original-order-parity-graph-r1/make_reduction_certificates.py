"""Produce small exact certificates by affine arithmetic, not CM counts."""
import json
from math import prod
from orientation import solve, orientations, moduli, exact_crt

INPUTS = [(9649, 7394, [149, 2441]), (95441, 84708, [23833, 2986]),
          (387089, 29597, [24116, 97081]), (1473041, 250332, [367673, 92212])]


def factor(n):
    out = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def scalar(p, A, P, n):
    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        x, y = P
        u, v = Q
        if x == u and (y+v) % p == 0:
            return None
        m = ((v-y)*pow(u-x, -1, p) if x != u else (3*x*x+A)*pow(2*y, -1, p)) % p
        X = (m*m-x-u) % p
        return X, (m*(x-X)-y) % p
    out = None
    while n:
        if n & 1:
            out = add(out, P)
        P = add(P, P)
        n //= 2
    return out


def main():
    rows = []
    pairs = []
    for p, root, orders in INPUTS:
        sides = []
        for r, n in zip((root, p-root), orders):
            A = -(3-r)**2 % p
            P = ((1+r) % p, 2*r % p)
            factors = factor(n)
            assert scalar(p, A, P, n) is None
            drops = {str(q): scalar(p, A, P, n//q) for q in factors}
            assert all(v is not None for v in drops.values())
            sides.append({'sqrt_two': r, 'curve_a4': A, 'point': P, 'order': n,
                          'factorization': factors, 'annihilation': None, 'prime_drops': drops})
        rows.append({'prime': p, 'sides': sides})
        pairs.append(orders)
    Pi = prod(p for p, _, _ in INPUTS)
    scenarios = []
    for L, h0 in [(1, 0), (16, 0), (16, 1)]:
        solution = solve(pairs, Pi, L, h0)
        candidates = []
        for bits in orientations(solution):
            minus, plus = moduli(pairs, bits)
            h, period = exact_crt(Pi, minus, plus, L, h0)
            candidates.append({'orientation_bits': bits, 'minus': minus, 'plus': plus,
                               'h': h, 'period': period})
        scenarios.append({'L': L, 'h0': h0, 'orientation_count': len(candidates), 'candidates': candidates})
    print(json.dumps({'curve': 'y^2=x^3-(3-r)^2*x', 'point': '(1+r,2*r)',
        'rows': rows, 'independent_prime_product': Pi, 'four_position_scenarios': scenarios,
        'scope': 'Exact finite-field orders of the literal reduction of R. Four independent primes, NOT the original fifteen-position Values. No new native Lean quotient-order theorem.'}, indent=2))

if __name__ == '__main__':
    main()
