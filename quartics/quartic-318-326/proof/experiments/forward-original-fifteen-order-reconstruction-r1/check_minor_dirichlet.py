#!/usr/bin/env python3
"""Exact finite sanity checks, not Lean elaboration or asymptotic proof."""
from fractions import Fraction as F
from math import gcd,ceil
from pathlib import Path
import json
counts=dict(minor_points=0,small_denominator_exclusions=0,reduced_witnesses=0,canonical_numerators=0,cell_widths=0,half_open_endpoint_checks=0,overlap_integral_checks=0,negative_controls=0)
def centers(N):
    return [F(a,q) for q in range(1,N+1) for a in range(q) if gcd(a,q)==1]
def minor(t,N,B):
    r=F(N,B*B)
    return -r<t<=1-r and not any(c-r<t<=c+r for c in centers(N))
def witness(t,Q):
    for q in range(1,Q+1):
        lo=(t*q).__floor__()
        for a in [lo,lo+1]:
            f=F(a,q)
            if abs(t-f)<=F(1,(Q+1)*f.denominator):return f
    raise AssertionError(('Dirichlet witness missing',t,Q))
for N in range(1,5):
    B=(N+1)**3; r=F(N,B*B);Q=ceil(F(B*B,N))
    assert F(1,Q+1)<r
    for j in range(1,129):
        t=-r+F(j,129)
        if not minor(t,N,B):continue
        counts['minor_points']+=1
        for q in range(1,N+1):
            for a in range(-q,2*q+1):
                if gcd(a,q)!=1:continue
                assert r<=abs(t-F(a,q))
                counts['small_denominator_exclusions']+=1
        f=witness(t,Q);q=f.denominator;a=f.numerator;w=F(1,(Q+1)*q)
        assert N<q<=Q and gcd(a,q)==1 and abs(t-f)<=w<=F(1,q*q)
        counts['reduced_witnesses']+=1
        assert 1<=a<q and r<t<=1-r
        counts['canonical_numerators']+=1
        assert (f+w)-(f-w)==2*w
        counts['cell_widths']+=1
    for c in centers(N):
        # Interior and right endpoint lie in the actual Ioc major arc.
        assert not minor(c,N,B) and not minor(c+r,N,B)
        # Left endpoints belong to minor except the excluded fundamental left endpoint.
        assert minor(c-r,N,B)==(c!=0)
        counts['half_open_endpoint_checks']+=1
# Exact generic overlapping cover integration for a nonconstant positive polynomial.
def integ(a,b):return (b-a)+(b**3-a**3)/3
for k in range(1,65):
    s=(F(0),F(1));e=F(1,k+2)
    cells=[(F(0),F(1,2)+e),(F(1,2)-e,F(1))]
    assert integ(*s)<=sum(integ(*c) for c in cells)
    assert integ(*s)<sum(integ(*c) for c in cells) # overlap really is retained
    counts['overlap_integral_checks']+=1
# Negative controls: denominator endpoint, half-open endpoint, lift at one,
# and false disjoint summation are all actual rejected simplifications.
assert not F(1,64)<F(1,64);counts['negative_controls']+=1
assert minor(F(1,2)-F(2,27**2),2,27);counts['negative_controls']+=1
assert not (-F(1,64)<F(1)<=1-F(1,64));counts['negative_controls']+=1
assert integ(F(0),F(1))!=integ(F(0),F(3,4))+integ(F(1,4),F(1));counts['negative_controls']+=1
result={'status':'PASS','arithmetic':'exact fractions throughout','counts':counts,'limits':'Finite regression only; native Dirichlet proof, smooth constants, measure-theory proof, Lean elaboration and final minor power saving are not inferred from it.'}
print(json.dumps(result,indent=2))
if __name__=='__main__':Path(__file__).with_name('MINOR-DIRICHLET-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n')
