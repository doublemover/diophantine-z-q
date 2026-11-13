"""Independent brute-force tests of graph completeness and exact CRT semantics."""
import itertools
import json
import math
import random
from orientation import solve, orientations, exact_crt, moduli


def brute_ok(pairs, bits, Pi, L, h0):
    # Independent criterion, no solver/merge helper.
    A = Pi**3 * math.lcm(*(row[bit] for row, bit in zip(pairs, bits)))
    B = math.lcm(*(row[1-bit] for row, bit in zip(pairs, bits)))
    return (math.gcd(A, B) == 1 and h0 % math.gcd(A, L) == 0
            and (h0-1) % math.gcd(B, L) == 0)


def compare(pairs, Pi, L, h0):
    graph = solve(pairs, Pi, L, h0)
    actual = set(orientations(graph))
    expected = {s for s in itertools.product((0, 1), repeat=len(pairs)) if brute_ok(pairs, s, Pi, L, h0)}
    assert actual == expected, (pairs, Pi, L, h0, actual, expected)
    if graph['satisfiable']:
        assert len(actual) == graph['orientation_count']
    for s in actual:
        minus, plus = moduli(pairs, s)
        h, period = exact_crt(Pi, minus, plus, L, h0)
        for offset in (0, 1, 17):
            t = h + offset*period
            assert t % (Pi**3*minus) == 0 and (t-1) % plus == 0 and (t-h0) % L == 0
    return len(expected)


def main():
    exhaustive = 0
    for values in itertools.product(range(1, 6), repeat=4):
        pairs = [values[:2], values[2:]]
        for Pi, L, h0 in itertools.product(range(1, 4), range(1, 6), range(5)):
            compare(pairs, Pi, L, h0)
            exhaustive += 1
    rng = random.Random(318326)
    for _ in range(1000):
        pairs = [(rng.randrange(1, 100), rng.randrange(1, 100)) for i in range(rng.randrange(1, 8))]
        compare(pairs, rng.randrange(1, 20), rng.randrange(1, 50), rng.randrange(50))
    fifteen = [([(1, 1)]*15, 1, 1, 0), ([(3, 5)]*15, 1, 1, 0),
               ([(3, 5)]*15, 1, 5, 1), ([(3, 5)]*15, 1, 5, 0)]
    for _ in range(8):
        fifteen.append(([(rng.randrange(1, 500), rng.randrange(1, 500)) for i in range(15)], 7, 16, 1))
    counts = [compare(*case) for case in fifteen]
    # Direct residues, not the gcd criterion, for all these small moduli.
    direct = 0
    for Pi, minus, plus, L, h0 in itertools.product(range(1, 4), range(1, 7), range(1, 7), range(1, 7), range(6)):
        period = math.lcm(Pi**3*minus, plus, L)
        residues = [h for h in range(period) if h % (Pi**3*minus) == 0 and (h-1) % plus == 0 and (h-h0) % L == 0]
        result = exact_crt(Pi, minus, plus, L, h0)
        assert residues == ([] if result is None else [result[0]])
        direct += 1
    # Strict improvement: old plus/L coprimality fails, exact residues work.
    strict = exact_crt(1, 3, 5, 5, 1)
    assert strict == (6, 15) and math.gcd(5, 5) != 1
    # Cross-neighbor obstruction despite each same-position pair being coprime.
    bad = [(2, 3), (3, 5), (5, 2)]
    assert all(math.gcd(a, b) == 1 for a, b in bad)
    assert not solve(bad, 1, 1, 0)['satisfiable']
    # Global Pi^3/L obstruction may not be omitted from minus-side tests.
    assert not solve([(1, 1)], 2, 8, 1)['satisfiable']
    # 1-valued orders, h0=0, non-squarefree orders, and both-side forcing.
    for args in [([], 1, 1, 0), ([(0, 1)], 1, 1, 0), ([(1, 1)], 0, 1, 0), ([(1, 1)], 1, 0, 0), ([(1, 1)], 1, 1, -1)]:
        try:
            solve(*args)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid domain accepted')
    print(json.dumps({'exhaustive_two_position_inputs': exhaustive, 'random_inputs': 1000,
        'full_fifteen_bruteforce_inputs': len(fifteen), 'fifteen_candidate_counts': counts,
        'direct_residue_crt_inputs': direct, 'strict_continuity_improvement': {'h': strict[0], 'period': strict[1]},
        'cross_neighbor_parity_obstruction': bad,
        'scope': 'Finite exact arithmetic and complete solver comparison, not prime production, a distribution theorem, or Lean verification.'}, indent=2))

if __name__ == '__main__':
    main()
