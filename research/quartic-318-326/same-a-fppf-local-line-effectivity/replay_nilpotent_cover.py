from itertools import product
import json

p = 5
zero = (0, 0, 0, 0)
one = (1, 0, 0, 0)
d = (0, 0, 1, 0)

def add(a, b):
    return tuple((x + y) % p for x, y in zip(a, b))

def scale(l, a):
    return tuple((l * x) % p for x in a)

def mul(a, b):
    return tuple(sum(a[j] * b[i-j] for j in range(i + 1)) % p for i in range(4))

n = 0
for a0, a1, y2, y3, f in product(range(1, p), range(p), range(p), range(p), range(p)):
    a = (a0, a1, 0, 0)
    y = (a0, a1, y2, y3)
    x = mul(add(one, scale(f, d)), y)
    t = mul(d, a)
    lam = lambda w: (pow(t[2], -1, p) * w[2]) % p
    diff = add(x, scale(-1, y))
    assert mul(d, d) == zero and t != zero
    assert diff == scale(f, t) and lam(t) == 1 and (lam(x) - lam(y)) % p == f
    n += 1
squares = {(a*a % p, 2*a*b % p) for a, b in product(range(p), repeat=2)}
assert (0, 1) not in squares
print(json.dumps({"ring": "F5[x]/x^4", "epsilon_image": "x^2", "tested_gauge_rows": n,
                  "epsilon_has_square_root_in_F5_dual": False, "source_only": True}, sort_keys=True))
