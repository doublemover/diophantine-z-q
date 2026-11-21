#!/usr/bin/env python3
"""Exact local norm bounds, metric scaling and nonprincipal ideal canary."""
from fractions import Fraction as Q
from math import prod
import json

def add(A,B):
    return A[0]+B[0],A[1]+B[1]
def neg(A):
    return -A[0],-A[1]
def mul(A,B):
    return A[0]*B[0]-5*A[1]*B[1],A[0]*B[1]+A[1]*B[0]
def norm(A):
    return A[0]**2+5*A[1]**2

one=(1,0); two=(2,0); alpha=(1,1)
p2=tuple(mul(u,v) for u in (two,alpha) for v in (two,alpha))
assert all(all(x % 2 == 0 for x in z) for z in p2)
combination=add(add(p2[1],neg(p2[3])),neg(p2[0]))
assert combination==two # p²=(2).
# A generator would have integer norm 2, impossible with coefficient b≠0
# since 5 b²>2, and impossible with b=0 since 2 is not a square.
assert all(norm((a,b))!=2 for a in range(-2,3) for b in range(-2,3))
p_inverse_coordinates=[tuple(Q(x,2) for x in z) for z in (two,alpha)]
assert p_inverse_coordinates==[(Q(1),Q(0)),(Q(1,2),Q(1,2))]
assert all(mul(two,z) in (two,alpha) for z in p_inverse_coordinates)
assert Q(2)**(-1)==Q(1,2)
assert 4*3-11==1
assert (22%3,22%11,12%3,12%11,(22+12)%33)==(1,0,0,1,1)

local_rows=unsupported=0
for Nw in (2,3,4,5,7,8,9,11,25,121):
    N=Q(Nw)
    for A in range(-5,6):
        for B in range(-5,6):
            for n in range(-B,A+1):
                u=N**(-n)
                x=N**(-(A-n))
                y=N**(-(B+n))
                assert x<=1 and y<=1
                assert x*u==N**(-A) and N**(-B)*u==y
                assert (1/u)==N**n
                if A==B==0:
                    assert u==1
                    unsupported+=1
                # Same rank-one coefficient after rational frame rescale.
                for C in (-7,-3,0,2,7):
                    assert (N**(n-C))==(N**n)*(N**(-C))
                local_rows+=1

# A common field extension: model finite factors by exact prime powers,
# with all e_i f_i summing to the same total local degree.
extensions=0
for n in range(-6,7):
    for Nw in (2,3,4,5,9,11):
        for shapes in (((2,1),(1,2)),((1,1),(3,1)),((2,2),),((1,4),)):
            assert sum(e*f for e,f in shapes)==4
            lhs=prod(Q(Nw)**(f*e*n) for e,f in shapes)
            assert lhs==(Q(Nw)**n)**4
            extensions+=1

print(json.dumps(dict(bezout=[4,-1], gluing_locales=[3,11,33],
   exact_fractional_order_rows=local_rows, no_support_rows=unsupported,
   degree_base_extension_rows=extensions, nonprincipal_canary={
       "field":"Q(sqrt(-5))","ideal":"(2,1+sqrt(-5))",
       "inverse_frame_norm_at_p":"1/2","p_squared_generator":combination},
   scope="lattice arithmetic only; no numerical model or stable height"),sort_keys=True,indent=2))
