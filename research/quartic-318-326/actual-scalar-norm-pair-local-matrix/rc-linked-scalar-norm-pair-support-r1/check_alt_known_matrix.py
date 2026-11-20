"""Exact GF(2) analysis of the known-support local tests; no unknown Z guesses."""
import json
from math import gcd, isqrt, prod
from pathlib import Path

src = Path(__file__).resolve().parent.parent / 'rc-linked-scalar-specialization-publish-r1'
data = json.loads((src/'EXACT-SCALAR-SPECIALIZATION.json').read_text())
h, J = data['first_passing_h'], data['J']
g = gcd(h,J)
assert h//g == 81
assert J//g == 2566827915619116471899843747792873596324159383802094955344492089413795992750334532240167202776488314896151365217289774312203906250

B = (5,11,17,163,661,733,1489,1861)
H = (131,6551,2470991,16782959)
qs = (*B,*H)
beta = prod(B)
Zfixed = prod((29,181,1346909,70850399941))
assert Zfixed == 1+17*beta*144
def is_prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
assert all(map(is_prime, (*qs,83,29,181,1346909,70850399941)))
def chi_bit(a,p):
    assert a%p
    return int(pow(a%p,(p-1)//2,p)==p-1)
labels = ['dyadic','3',*[f'beta-{p}' for p in B],'Lprime-83']
rows = [[int(q%8 in (5,7)) for q in qs],[chi_bit(q,3) for q in qs]]
rows += [[chi_bit(3*beta//p,p) if q==p else chi_bit(q,p) for q in qs] for p in B]
rows += [[chi_bit(q,83) for q in qs]]
assert rows[-1][-len(H):] == [0]*len(H) and chi_bit(7,83)==0
assert chi_bit(3*beta,83)==0
masks = [sum(a<<i for i,a in enumerate(row)) for row in rows]
fibres = [[] for _ in range(2**len(rows))]
for x in range(2**len(qs)):
    v = sum(((x&m).bit_count()%2)<<j for j,m in enumerate(masks))
    fibres[v].append(x)
assert all(len(xs)==2 for xs in fibres)
k = fibres[0][1]
assert all(x^y==k for x,y in fibres)
bits = [q for i,q in enumerate(qs) if k>>i&1]
assert k==1643 and prod(bits)==158389989243518750905
primes = (3,*B,83)
fixed_phases = {str(p): (-1 if chi_bit(Zfixed,p) else 1) for p in primes}
def lim(r):
    n=2**r
    return n+1-isqrt(4*n)
assert (lim(15),lim(47)) == (32407,140737464628763)
print(json.dumps(dict(columns=qs,row_labels=labels,rows=rows,row_masks=masks,
    rank=len(rows),lift_count_for_every_rhs=2,kernel_mask=k,kernel_primes=bits,
    kernel_product=prod(bits),fixed_normalizer_Z_signs=fixed_phases,
    pole_lower_bounds=dict(h=lim(15),translated=lim(47))),indent=2))
