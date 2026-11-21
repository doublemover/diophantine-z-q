import json
from math import gcd, isqrt, prod
from pathlib import Path
import sys

author = json.loads(Path(sys.argv[1]).read_text())
N = 205042530
level = (2,3,5,7,11,37,2399)
p_a, p_b = (415721,9807649)
for p in level + (p_a, p_b):
    assert all(p % n for n in range(2,isqrt(p)+1))
assert N == prod(level)
roots = (0,-76768,407)
# At 2, x=4X,y=8Y+4X gives a1=1 and coefficients below.
a2 = (76768-407-1)//4
a4 = -76768*407//16
assert a2 % 2 == a4 % 2 == 0 and a2*4 == 76768-407-1
# a_p is +1 at a split node. At odd p its two tangents have slopes
# squaring to the repeated root minus the unused root.
a = [1]
for p in level[1:]:
    rr = [v%p for v in roots]
    assert sorted(rr.count(v) for v in rr) == [1,2,2]
    dup = next(v for v in rr if rr.count(v)==2)
    rem = next(v for v in rr if rr.count(v)==1)
    a.append(1 if any((u*u-dup+rem)%p==0 for u in range(p)) else -1)
assert a == author['ap']
squares = {p:{u*u%p for u in range(p)} for p in level[1:]}

def sg(x,p):
    # Binary Jacobi reciprocity algorithm, deliberately not Euler powers.
    x %= p
    s = 1
    while x:
        while x%2==0:
            x //= 2
            if p%8 in (3,5): s = -s
        if x%4 == p%4 == 3: s = -s
        x,p = p%x,x
    return s if p==1 else 0
for q in (p_a,p_b): assert q%8==1 and gcd(q,2*N)==1
phase = [[1]+[sg(l,q) for l in level[1:]] for q in (p_a,p_b)]
assert [x['primes'] for x in author['pilot_phase_rows']] == phase
fixed, forced, common = [], [], []
for d in range(2,isqrt(N)+1):
    if N%d==0: fixed.extend((d,N//d))
fixed += [N]
all_div = sorted(fixed); assert len(all_div) == 127
fixed = []
for d,row in zip(all_div, author['all_nontrivial_W'], strict=True):
    stable = all(-d % l in squares[l] for l in level[1:] if d%l)
    eigen = prod(-s for l,s in zip(level,a) if d%l==0)
    signs = [sg(-d,q) for q in (p_a,p_b)]
    assert (row['d'],row['fixed'],row['eigen'],row['pilot_signs']) == (d,stable,eigen,signs)
    if stable:
        fixed.append(d)
        if eigen==1:
            forced.append(d)
            if signs==[-1,-1]: common.append(d)
assert fixed == author['fixed'] and forced == author['forced'] and common == author['inert_in_both']
for p,r in [(3,1),(37,9),(2399,1066)]:
    assert (r*r+770) % p==0 and N%p==0 and 770%p
out=dict(level=N,ap=a,mod2_node=[1,a2%2,a4%2],phase=phase, fixed_count=len(fixed),
         forced=forced, inert_in_both=common, w770_odd_complement_roots={3:1,37:9,2399:1066}, total_nonidentity=len(all_div))
print(json.dumps(out,indent=2))
