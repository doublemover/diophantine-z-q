#!/usr/bin/env python3
from fractions import Fraction as Q
from itertools import combinations
from math import factorial, gcd, isqrt, lcm, prod
import json

bs = (0,32,-343,76832)
gaps = tuple(abs(a-b) for a,b in combinations(bs,2))
d0 = lcm(*gaps)
assert d0 == 2765952000 and 420*d0*d0*512 < 2**81
forms = [(0,1),(1,0),(1,-1),(1,-2401),(32,343)]
dets = tuple(abs(a*d-b*c) for (a,b),(c,d) in combinations(forms,2))
bad=(2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801)
def prime(p): return p>1 and all(p%v for v in range(2,isqrt(p)+1))
def strip(n):
    for p in bad:
        while n%p==0:
            n//=p
    return n
assert all(map(prime,bad)) and all(strip(d)==1 for d in dets)
B=prod(bad); C=2**28*3**6
assert (B,C)==(11185621387570686764517810,195689447424)
assert max(C*C,64*C,2304*C,8*1727*C)<B
assert B>=max(6000**2,1600) and B**5>=145000
assert 2*(1708*B+68)<B**6 # monotonically stronger for any S>=B
weights=(Q(1),Q(1),Q(1,7),Q(1,80))
W=sum(weights); V=960+sum(w*abs(b) for w,b in zip(weights,bs))
assert W+V/686<6 and W*686+V<3500 and 76832-686>76000
assert Q(12)/(2**3*2*6**3)>=Q(1,288)
interior=Q(960,7)*76000*16**2/(2*3500**3)
assert interior>Q(1,512)
def lower_exp(x,N):
    return sum(x**k/factorial(k) for k in range(N+1))
for x,y,N in [(Q(3,4),2,2),(Q(3),14,4),(Q(7),576,12),(Q(2),7,5)]:
    assert lower_exp(x,N)>y
assert 81*Q(3,4)<64
print(json.dumps(dict(contact_gaps=gaps, determinant_values=dets, metric_clearing=d0,
                      arch_bound=420*d0*d0*512, curvature_interior_lower=str(interior),
                      bad_product=B, level_factor=C, terminal_exact_thresholds=True),indent=2))
