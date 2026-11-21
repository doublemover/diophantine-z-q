"""Independent exact square-set check of the literal split Jacobian."""
from functools import lru_cache
from math import isqrt, prod

beta_part, beta_other, p, q = 41579528353, 4921145, 114649, 119851
beta = beta_part * beta_other
d = beta * p * q
primes_d = (5, 11, 17, 163, 661, 733, 1489, 1861, p, q)
global_basis = (-1, 2, 3, *primes_d)
assert d == 2811626664334219040035976315 == prod(primes_d)
assert all(all(l % i for i in range(2, isqrt(l) + 1)) for l in (2, 3, *primes_d))

@lru_cache
def square_residues(l):
    return frozenset(i * i % l for i in range(l))

def bits_at(n, l):
    assert n
    if l == -1:
        return int(n < 0)
    parity = 0
    while n % l == 0:
        parity ^= 1
        n //= l
    if l == 2:
        return parity | ({1: 0, 3: 3, 5: 2, 7: 1}[n % 8] << 1)
    return parity | (int(n % l not in square_residues(l)) << 1)

def label(x):
    dif = [x, x - d, x - 9*d]
    if 0 in dif:
        i = dif.index(0)
        dif[i] = prod(t for t in dif if t)
    return dif

def span(vectors):
    a = {0}
    for v in vectors:
        a |= {u ^ v for u in a}
    return a

def row_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            leftmost = row & -row
            if leftmost not in pivots:
                pivots[leftmost] = row
                break
            row ^= pivots[leftmost]
    return len(pivots)

def dot(a, b):
    return (a & b).bit_count() % 2

def location(a, b, l, width):
    return bits_at(a,l) | (bits_at(b,l) << width)

rows = []
target = (beta, -beta_other*q, -beta_part*q)
for l in global_basis:
    width = 1 if l < 0 else (3 if l == 2 else 2)
    xs = (0,) if l < 0 else ((0,d,-3) if l == 2 else ((d,3) if l == 3 else (0,d)))
    vectors = []
    for x in xs:
        a,b,c = label(x)
        assert bits_at(a,l) ^ bits_at(b,l) ^ bits_at(c,l) == 0
        vectors.append(location(a,b,l,width))
    local_span = span(vectors)
    assert len(local_span) == (2 if l < 0 else (8 if l == 2 else 4))
    assert location(*target[:2],l,width) in local_span
    columns = [location(g,1,l,width) for g in global_basis]
    columns += [location(1,g,l,width) for g in global_basis]
    for functional in range(1, 1 << (2*width)):
        if all(not dot(functional,v) for v in local_span):
            rows.append(sum(dot(functional,c) << i for i,c in enumerate(columns)))
    print(f"place {l:6}: |Kummer image|={len(local_span)}, witnesses={xs}")
n = 2 * len(global_basis)
r = row_rank(rows)
assert (r,n)==(23,26)
assert beta not in (1,d)
counts = tuple(1+sum(y*y%l == x*(x-d)*(x-9*d)%l for x in range(l) for y in range(l))
               for l in (7,53))
assert counts == (8,52)
print(f"matrix rank={r}/{n}, Selmer dimension={n-r}")
print(f"literal marked triple={target}")
print(f"J(F7), J(F53) orders={counts}")
