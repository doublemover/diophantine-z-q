from fractions import Fraction as Q
from itertools import combinations
from math import prod
from pathlib import Path
import json
import sys

rows = json.loads(Path(sys.argv[1]).read_bytes())
beta = 204618888056724185
assert rows['beta'] == beta
primes = set(range(2,325))
for p in range(2,19):
    if p in primes:
        primes.difference_update(range(p*p,325,p))
required = {}
for p in sorted(primes):
    if p < 7 or beta % p == 0:
        continue
    squares = {x*x % p for x in range(1,p)}
    if beta % p in squares or (-3) % p not in squares:
        continue
    required[p] = squares
assert set(required) == {r['p'] for r in rows['small_prime_rows']}
assert len(required) == len(rows['small_prime_rows']) == 15
for r in rows['small_prime_rows']:
    p,q = r['p'],r['q']
    s = required[p]
    assert 0 < q < p and q not in s
    x1 = (12*q*q+3)*pow(2+7*q,-1,p) % p if (2+7*q)%p else None
    if x1 is not None and x1!=1:
        ff = (x1+3)*pow(x1-1,-1,p) % p
    else:
        ff = 3*(q+1)*(4*q+3)*pow((3*q-1)*(4*q-1),-1,p) % p
    gg = -3*(4*q*q+1)*pow((4*q-1)*(4*q+3),-1,p) % p
    assert beta%p == r['beta_mod_p']
    assert r['betaF'] == beta*ff%p in s
    assert r['betaG'] == beta*gg%p in s
A=(Q(-1),Q(-3,4),Q(1,3),Q(1,4))
S=[abs((x-y).numerator*(x-y).denominator) for x,y in combinations(A,2)]
S += [abs((4*x*x+1).numerator*(4*x*x+1).denominator) for x in A]
assert all(n>0 for n in S)
for n in S:
    for p in (2,3,5,13):
        while n%p == 0:
            n//=p
    assert n==1
assert prod((131,6551,2470991,16782959))%8==5
assert all(p%5 in (1,4) for p in (131,6551,2470991,16782959))
print('15 complete useful-open local residue witnesses; branch-collision support {2,3,5,13}; visible theta product 5 mod 8.')
