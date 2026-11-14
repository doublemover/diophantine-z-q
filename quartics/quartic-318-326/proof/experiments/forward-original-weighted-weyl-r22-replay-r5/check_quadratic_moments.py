#!/usr/bin/env python3
"""Exact finite moment arithmetic. No floating integration or local Lean."""
from collections import Counter
from math import isqrt
from itertools import product
from pathlib import Path
import json
cnt=dict(square_fibers=0,signed_injections=0,zero_strata=0,energy_budgets=0,subset_moments=0,coefficient_cancellation=0,no_alias_orthogonality=0,amgm_products=0,original_rectangles=0,negative_controls=0)
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
for H in range(13):
    I=list(range(-H,H+1));fib={}
    for x,y in product(I,repeat=2):fib.setdefault(x*x-y*y,[]).append((x,y))
    for n,ps in fib.items():
        image=[(x-y,x+y) for x,y in ps]
        assert len(set(image))==len(ps) and all(u*v==n and abs(u)<=2*H and abs(v)<=2*H for u,v in image)
        cnt['signed_injections']+=len(ps);cnt['square_fibers']+=1
        if n:
            assert len(ps)<=2*len(divisors(abs(n)))
        else:
            assert len(ps)<=2*(2*H+1)
            assert all(x==y or x==-y for x,y in ps)
            cnt['zero_strata']+=1
    E=sum(len(ps)**2 for ps in fib.values())
    D=max([2*len(divisors(n)) for n in range(1,H*H+1)]+[0])
    assert E<=(2*H+1)**2*(D+4);cnt['energy_budgets']+=1
    subsets=[[],I,I[:len(I)//2],I[::2],[x for x in I if x>=0],[x for x in I if x%3!=0]]
    for s in subsets:
        energies=Counter(x*x-y*y for x,y in product(s,repeat=2))
        e=sum(v*v for v in energies.values())
        assert e<=E;cnt['subset_moments']+=1
        for c in [-5,-1,1,2,7]:
            fr=Counter(c*(x*x-y*y) for x,y in product(s,repeat=2))
            assert sum(v*v for v in fr.values())==e;cnt['coefficient_cancellation']+=1
            # Exact finite-character orthogonality at order M: no alias since
            # all second-difference frequencies have magnitude <=2|c|H²<M.
            M=4*abs(c)*H*H+1
            assert sum(v*w for a,v in fr.items() for b,w in fr.items() if (a-b)%M==0)==e
            cnt['no_alias_orthogonality']+=1
for a,b,c,d in product(range(-3,4),repeat=4):
    assert 4*a*b*c*d<=a**4+b**4+c**4+d**4;cnt['amgm_products']+=1
roots=[1,1j,-1,-1j]
# Gaussian-integer arithmetic is exact in these small bounded tests.
def qsum(s,c,k):return sum(roots[(c*x*x*k)%4] for x in s)
I=[-1,0,1]
for kap in [-3,-1,0,2]:
    for masks in [(I,I,I,I,I),([-1,0],I,[0,1],[-1,1],I),([],I,I,I,I)]:
        for k in range(4):
            brute=sum(roots[((a*a+b*b-c*c-d*d-kap*e*e)*k)%4] for a,b,c,d,e in product(*masks))
            fact=1
            for s,c in zip(masks,[1,1,-1,-1,-kap]):fact*=qsum(s,c,k)
            assert brute==fact;cnt['original_rectangles']+=1
# Zero c cannot be cancelled; zero fiber cannot use divisors(0);
# signed factor map is not surjective due parity; sup cannot pass an integral.
s=[-1,0,1];energy=sum(v*v for v in Counter(x*x-y*y for x,y in product(s,repeat=2)).values())
assert len(s)**4!=energy;cnt['negative_controls']+=1
assert len([(x,y) for x,y in product(s,repeat=2) if x*x-y*y==0])>0;cnt['negative_controls']+=1
assert (1,2) not in {(x-y,x+y) for x,y in product(range(-3,4),repeat=2)};cnt['negative_controls']+=1
assert max(1,0)+max(0,1)>max(1+0,0+1);cnt['negative_controls']+=1
out={'status':'PASS','counts':cnt,'limits':'Exact finite collision counts, signed injection, formal finite-character orthogonality and original rectangular identities only. No smooth weighted Abel, supremum estimate, real analytic subpower proof, local Lean or final o(B^3) inferred.'}
print(json.dumps(out,indent=2));Path(__file__).with_name('QUADRATIC-MOMENT-REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n')
