#!/usr/bin/env python3
"""Literal h factorization, signed norm-depth controls and known-support exhaustion."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd, isqrt, prod
from pathlib import Path
import json
import runpy

root = Path(__file__).resolve().parent.parent
def load(rel, digest):
    p = root / rel
    assert sha256(p.read_bytes()).hexdigest() == digest
    with redirect_stdout(StringIO()):
        return runpy.run_path(str(p))

F = dict([(2,6),(3,8)] + [(p,1) for p in [
    5,11,13,17,29,31,41,47,53,73,89,131,337,389,1231,4261,
    1041427,472879111,26773696669,739721042333238923]])
certificates = {
    1041427: {2:1,3:2,47:1,1231:1},
    472879111: {2:1,3:1,5:1,11:1,719:1,1993:1},
    26773696669: {2:2,3:1,56369:1,39581:1},
    39581: {2:2,5:1,1979:1},
    56369: {2:4,13:1,271:1},
    739721042333238923: {2:1,11:1,8951:1,3756416461001:1},
    8951: {2:1,5:2,179:1},
    3756416461001: {2:3,5:3,7:1,536630923:1},
    536630923: {2:1,3:2,71:1,599:1,701:1},
}
witness = {}
def prime(p):
    if p < 5000:
        assert p >= 2 and all(p % j for j in range(2,isqrt(p)+1))
    elif p not in witness:
        fac = certificates[p]
        assert prod(q**a for q,a in fac.items()) == p-1
        for q in fac: prime(q)
        # The displayed Fermat+gcd tests prove exact primality,
        # not probable primality or an invocation of ECM.
        w = next(a for a in range(2,100) if pow(a,p-1,p)==1 and
                 all(gcd(pow(a,(p-1)//q,p)-1,p)==1 for q in fac))
        witness[p] = w
for p in F: prime(p)

depth = load('linked-detector-w37-depth-r1/check_actual_shallow_formal.py',
             '4302feb27fa532f4e713e512a819c88c975a02993782f4ab9b346b590724ed63')
h, field = depth['h'], depth['field']
assert prod(p**s for p,s in F.items()) == h
old = load('linked-detector-known16-exhaustion-r1/check_fixed_h_known16.py',
           '8e61ecaf53ffaa28fda06afde0012349224359998d81ef1e77e4fb73d5cecffd')
P0 = old['P0']
chi = old['chi']

def roots(p):
    if chi(2,p)==-1: return [None]
    if p < 5000: r = next(u for u in range(p) if u*u%p==2)
    else:
        assert p%8==7
        r = pow(2,(p+1)//4,p)
        assert r*r%p==2
    return sorted((r,p-r))

rows = []
additional_possible = []
fixed = 2*3*5*7*17*2399*407*2398*439
for p,s in F.items():
    if fixed%p==0: continue
    arms=[]
    for r in roots(p):
        r2 = None if r is None else r+p*(((2-r*r)//p)*pow(2*r,-1,p)%p)
        if r2 is not None: assert r2*r2%(p*p)==2
        _,point,_,formal = field(p,r2)
        Q = point(2*h)
        V = point(2*h//p**s)
        if formal(Q):
            assert formal(V), (p,r) # Verified, including all inert positive arms.
            assert V[0]%p==V[1]%p==0
            lo=s+1+(V==(0,0))
            assert Q==(0,0) and s>=1
            bounds=[lo,lo] if V!=(0,0) else [lo,None]
            arms.append({'root':r,'full_Q':'O','cofactor_z_mod_p2':V,
                         'norm_arm_depth_interval':bounds})
        else:
            x,y=Q
            x=[v%p for v in x]
            y=[v%p for v in y]
            assert x!=[0,0], (p,r)   # Proves type 0, not a hidden opposite pole.
            arms.append({'root':r,'full_Q':[x,y],'norm_arm_depth_interval':[0,0]})
    f=2 if len(arms)==1 else 1
    dmin=f*sum(a['norm_arm_depth_interval'][0] for a in arms)
    hi=[a['norm_arm_depth_interval'][1] for a in arms]
    dmax=None if None in hi else f*sum(hi)
    indices=[i+1 for i,(a,b) in enumerate(zip(old['a'],old['b']))
             if a*b%p and chi(-a*b,p)==1]
    if p not in P0 and indices and (dmax is None or dmax >= 4):
        additional_possible.append(p)
    rows.append({'p':p,'h_exponent':s,'arms':arms,'norm_depth_interval':[dmin,dmax],
                 'forms_with_square_T_root':indices})
assert additional_possible==[29,41,47,73,337,389]
possible=sorted(set(P0)|set(additional_possible))
ordinary=prod(p for p in possible if p not in (5,7))
assert all(gcd(ordinary,old['delm'][i][j])==1 for i in range(4)
           for j in range(4) if i!=j)
# The old free p=5 T=1 gate applies only in its old universe.
# Rebuild all possible exact *normalized* 5-local squareclass tags.
a,b,delm=map(old.get,('a','b','delm'))
from itertools import product
def scal(n):
    if n==0: return [(e,ch) for e,ch in product(range(2),(-1,1))]
    v=0
    while n%5==0: n//=5;v+=1
    return [(v%2,chi(n,5))]
tags={
    'D=0 mod 5': {tuple((0,chi(A,5)) for A in a)},
    'T=0 mod 5': {tuple((0,chi(B,5)) for B in b)},
    'T=1 mod 5': {tuple((0,chi(A+B,5)) for A,B in zip(a,b))},
    'T=4 mod 5': set(),
}
for x in range(125):
    vals=[(A*(-1+5*x)+B)%625 for A,B in zip(a,b)]
    assert vals.count(0)<=1
    tags['T=4 mod 5'].update(product(*map(scal,vals)))
assert list(map(len,tags.values()))==[1,1,1,16]

def subsets(mask):
    m=mask
    while True:
        yield m
        if m==0: break
        m=(m-1)&mask

def eval_widened(saturation, tag):
    P=[p for p in possible if p not in saturation and p not in (5,7)]
    base=[A//prod(p for p in P if A%p==0) for A in a]
    def pp(M): return [p for k,p in enumerate(P) if M>>k&1]
    C=[]
    for i,(A,B) in enumerate(zip(a,b)):
        U=sum(1<<j for j,p in enumerate(P) if A%p and chi(-A*B,p)==1)
        e,ch=tag[i]
        scale=2 if i==0 else 1
        cs={}
        for M in subsets(U):
            r=base[i]*prod(pp(M))*5**e
            if r//scale%24==A//scale%24 and chi(r,17)==chi(A,17) and chi(r//5**e,5)==ch:
                cs[M]=r
        C.append(cs)
    def pair(i,u,j,v):
        return (not (u&v) and
                all(chi(C[j][v],p)==chi(delm[i][j]*a[i],p) for p in pp(u)) and
                all(chi(C[i][u],p)==chi(delm[j][i]*a[j],p) for p in pp(v)))
    R=[()]
    join=[]
    for j in range(4):
        R=[(*t,u) for t,u in product(R,C[j]) if all(pair(i,r,j,u) for i,r in enumerate(t))]
        join.append(len(R))
    return [[C[i][x] for i,x in enumerate(t)] for t in R],join

T=[11,37,2399]
result=[]
for mask in range(8):
    S=[p for i,p in enumerate(T) if mask>>i&1]
    for branch,phase in tags.items():
        tau=[]
        output=set()
        for tag in sorted(phase):
            R,join=eval_widened(S,tag)
            output.update(map(tuple,R))
            tau.append({'normalized_local_tags':tag,'join_counts':join})
        expected={(2,1,2399,407)} if mask==7 and branch=='D=0 mod 5' else set()
        assert output==expected
        result.append({'saturated_non5':S,'p5_branch':branch,'phase_controls':tau,
                       'all_four':sorted(output)})
print(json.dumps({'h':str(h),'factorization':F,'n_minus_one_factors':certificates,
                  'prime_witness':witness,'fixed_exception_integer':fixed,
                  'all_h_support_rows':rows,'new_potential_h_support':additional_possible,
                  'widened_universe':possible,'saturation_results':result},indent=2))
