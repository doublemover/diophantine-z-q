#!/usr/bin/env python3
"""Independent positive-denominator trace and direct CRT for all visible switches."""
import argparse
from hashlib import sha256
import json
from math import isqrt, prod
from pathlib import Path

root = Path(__file__).resolve().parents[2] / 'joined-work-20261120'
parser = argparse.ArgumentParser()
parser.add_argument('--proof-dir', type=Path,
                    default=root/'rc-linked-scalar-H-visible-switch-cycles-r1')
parser.add_argument('--small', type=Path,
                    default=root/'rc-linked-scalar-specialization-r1/ACTUAL-THETA-MODULAR-ROWS.json')
parser.add_argument('--large', type=Path,
                    default=root/'rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json')
args = parser.parse_args()

def verify(path, pin):
    data = path.read_bytes()
    assert sha256(data).hexdigest() == pin
    return data

directory = args.proof_dir
verify(directory/'NO-SECOND-ORBIT-WITHOUT-SPLITTING-HIDDEN-H.md',
       '1585a8a2665d75666ff57f90c030fa02eafd4a8293e6e11a11e0727d513edd28')
expected = json.loads(verify(directory/'ACTUAL-VISIBLE-SWITCH-CYCLES.json',
                            'c1441d9b2f7123a911e83db8ed5524948fa0979a7267cb62421af723dcbcb9ab'))
small = json.loads(verify(args.small, 'b93ba6c7bc264368162e145e695e796f3aeddd9f10f2f3bdee09792293be7134'))
large = json.loads(verify(args.large, '1faac663c3b3ee2913668db3998265530c9d56bdd33e5207c9a4cb0b825c97f0'))
assert len(small)==1 and small[0]['prime']==6551
assert [r['prime'] for r in large]==[2470991,16782959]

B = prod([5,11,17,163,661,733,1489,1861])
R, M = 4376874610839020, 1+2448*B
S = isqrt(B)
assert 4*B == 187*R and B == expected['beta']
assert S == expected['sqrt_floor'] and S*S < B < (S+1)**2 and M == expected['M']

rows = [(131,1), (6551,small[0]['W']), *[(r['prime'],r['W_mod_p_squared'] % r['prime']) for r in large]]
assert [p for p,_ in rows]==expected['primes']
lifts=[]
for p,W in rows:
    assert p>2 and all(p % i for i in range(2,isqrt(p)+1))
    c=12*W*pow(M,-1,p)%p
    t=pow(c,-1,p)
    # Scan the p possible first-order digit only conceptually. The derivative gives
    # the same unique digit, but direct Hensel validation below is independent.
    digit=(-(t*t-B)//p)*pow(2*t,-1,p)%p
    T=t+p*digit
    assert (t*t-B)%p==0 and (T*T-B)%(p*p)==0
    lifts.append((p*p,T))
    assert [p,W,c,t,T] in expected['oriented_roots_p_W_cmodp_tmodp_tliftmodp2']

def step(state):
    # Independently normalize to a strictly positive denominator, retaining a
    # separate sign on sqrt(B). Floor correction is only needed when the
    # negative sqrt sign perturbs an integer partial quotient downwards.
    a,sign,c=state
    f,r=divmod(a+sign*S,c)
    if sign<0 and r==0:
        f-=1
    residual=a-f*c
    d,r=divmod(B-residual**2,c)
    assert not r and d
    return (-residual,sign,d) if d>0 else (residual,-sign,-d)

def exact_trail(initial, forbidden):
    first_index={}
    at=initial
    while at not in first_index:
        assert at not in forbidden
        first_index[at]=len(first_index)
        at=step(at)
    return len(first_index),first_index[at],at,first_index

def signed_denominator(state):
    a,sign,c=state
    return [a*sign,c*sign]

length,index,at,principal=exact_trail((0,1,1),{})
assert [length,index,signed_denominator(at)] == [
    expected['principal'][k] for k in ('visited','repeat_index','repeat')]
results=[]
for mask in range(1,16):
    item=expected['switches'][mask-1]
    assert item['mask']==mask and not item['principal_intersection']
    pool=[row for j,row in enumerate(lifts) if mask>>j&1]
    Q=prod(q for q,_ in pool)
    P=sum(T * (Q//q) * pow(Q//q,-1,q) for q,T in pool)%Q
    assert [P,Q]==item['start'] and Q==item['d']**2 and (P*P-B)%Q==0
    length,index,at,other=exact_trail((P,1,Q),principal)
    assert [length,index,signed_denominator(at)] == [
        item[k] for k in ('visited','repeat_index','repeat')]
    results.append([mask,length,index])
    del other

print(json.dumps({'principal_states':len(principal),'disjoint_switches':results},indent=2))
