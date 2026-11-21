"""Exhaust every old graph and reserve bit row through five old neutral primes."""
from itertools import combinations
from collections import Counter
import json


def matrix(m, mask):
    rows = [1 << i for i in range(m)]
    for j, (u, v) in enumerate(combinations(range(m), 2)):
        if (mask >> j) & 1:
            t = (1 << u) | (1 << v)
            rows[u] ^= t
            rows[v] ^= t
    return rows


def invertible(rows):
    rows = rows[:]
    for i in range(len(rows)):
        for j in range(i, len(rows)):
            if (rows[j] >> i) & 1:
                rows[i], rows[j] = rows[j], rows[i]
                break
        else:
            return False
        for j in range(i + 1, len(rows)):
            if (rows[j] >> i) & 1:
                rows[j] ^= rows[i]
    return True


def append(rows, b):
    m = len(rows)
    top = [x ^ (((1 << m) | (1 << i)) if (b >> i) & 1 else 0)
           for i, x in enumerate(rows)]
    return top + [(1 << m) ^ b ^ ((b.bit_count() % 2) << m)]


def mrun(m):
    c = Counter()
    for g in range(1 << (m * (m-1) // 2)):
        rows = matrix(m, g)
        good = [b for b in range(1 << m) if invertible(append(rows, b))]
        assert good
        if m % 2:
            # If m+1 is even both last old bit values can be prescribed.
            assert {b >> (m-1) for b in good} == {0, 1}
            assert len(good) % 2 == 0
        else:
            # Multiaffine diagonal polynomial has total XOR 1.
            assert len(good) % 2 == 1
        c[len(good)] += 1
    return {'old_vertices': m, 'all_old_graphs': sum(c.values()),
            'graphs_by_number_good_reserve_rows': sorted(c.items())}


res = {'scope': 'finite GF(2) graph replay, not prime statistics or rank',
       'graphs': [mrun(m) for m in range(6)]}
print(json.dumps(res, indent=2, sort_keys=True))
