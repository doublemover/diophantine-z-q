"""Exact auxiliary arithmetic checks; not a Lean proof or theorem acceptance."""
from collections import defaultdict

def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for m,c in p.items(): out[m] += c
    return {m:c for m,c in out.items() if c}
def scale(c,p): return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    out = defaultdict(int)
    for a,c in p.items():
        for b,d in q.items(): out[tuple(x+y for x,y in zip(a,b))] += c*d
    return {m:c for m,c in out.items() if c}
a,b,c,d = [{tuple(int(i==j) for i in range(4)):1} for j in range(4)]
T=add(scale(2,a),c)
N=add(mul(a,a),mul(a,c),scale(210,mul(b,b)),scale(210,mul(b,d)),scale(-1,mul(c,c)),scale(42,mul(d,d)))
D=add(scale(5,mul(c,c)),scale(-840,mul(b,b)),scale(-840,mul(b,d)),scale(-168,mul(d,d)))
assert not add(mul(T,T),scale(-4,N),scale(-1,D))
assert all((2*x*x-1)%5 != 0 for x in range(5))
assert all((5*x*x-4)%7 != 0 for x in range(7))
print('PASS: exact original trace/norm identity and exhaustive mod5/mod7 obstructions; no Lean validation.')
