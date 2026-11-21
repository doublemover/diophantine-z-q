"""Independent rational check of the sealed unchanged-metric curvature data."""
import hashlib
import json
import sys
from fractions import Fraction as F
from itertools import combinations
from math import factorial, prod
from pathlib import Path

raw = Path(sys.argv[1]).read_bytes()
assert hashlib.sha256(raw).hexdigest() == "1fbdd11edbbe879772594fde719b68aae7accc3f75c24b8ac160a5c6db5eaecb"
m = json.loads(raw)
b = (0, 32, -343, 76832)
w = (F(1), F(1), F(1, 7), F(1, 80))
c, cap = 960, 10**6
assert len(m["finite_rows"]) == 44
end = 0
mins = []
for x, y, n, den in m["finite_rows"]:
    assert x == end < y
    end = y
    d = [0 if x <= abs(a) <= y else min(abs(abs(a)-x), abs(abs(a)-y)) for a in b]
    upper = c + sum(u*(y+abs(a)) for u,a in zip(w,b))
    N = c*sum(w[i]*prod(d[j] for j in range(4) if j != i) for i in range(4))
    N += sum(w[i]*w[j]*(b[i]-b[j])**2*prod(d[k] for k in range(4) if k not in (i,j))
             for i,j in combinations(range(4), 2))
    lower = N/(2*upper**3)
    assert lower == F(n, den) and lower >= 64
    mins.append(lower)
assert end == cap
assert min(mins) == F(3050674698402471832275200, 47555288628475010599937)
for a in b:
    assert 1-F(abs(a), cap) >= F(9, 10)
assert sum(w)+(c+sum(u*abs(a) for u,a in zip(w,b)))/cap <= F(11,5)
tail = c*sum(w)*F(9,10)**3/(2*F(11,5)**3)
assert tail == F(2639709, 37268) > 64
D = 2765952000
C = F(4*D**2, 25725)
assert C.denominator == 1 and C == m["same_finite_divisor"] == 1189580636160000
assert (exp_partial := sum(F(1, factorial(i)) for i in range(7))) == F(1957, 720)
assert 420*D**2/(64*C) == F(2701125,64) < exp_partial**11
print("PASS: 44 exact cells, tail, unchanged finite divisor, strict +11 arithmetic")
