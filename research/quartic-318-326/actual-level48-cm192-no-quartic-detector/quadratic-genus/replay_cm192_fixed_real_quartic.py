#!/usr/bin/env python3
"""Exact Minkowski/class-number and fixed unit checks; no selected class arithmetic."""
from fractions import Fraction as Q
from itertools import product
from math import prod
import json


def mul(x,y):
    a,b,c,d=x; e,f,g,h=y
    # Basis (1,r,w,rw) with r²=3, w²=w+4.
    z=[0]*4
    for i,u in enumerate(x):
        for j,v in enumerate(y):
            j0=(i^j)&1
            m=3 if i&j&1 else 1
            if i&j&2:
                z[j0]+=4*m*u*v
                z[j0+2]+=m*u*v
            else:
                z[i^j]+=m*u*v
    return tuple(z)


def norm(x):
    a,b,c,d=x
    A=a*a+4*c*c-3*(b*b+4*d*d)
    B=2*a*c+c*c-3*(2*b*d+d*d)
    return A*A+A*B-4*B*B


def leg(a,p):
    return {1:1,p-1:-1}[pow(a%p,(p-1)//2,p)]


elts={2:(-1,-2,0,1),9:(0,1,0,0),13:(-2,-1,-2,2)}
assert {p:abs(norm(x)) for p,x in elts.items()}=={2:2,9:9,13:13}
ds=12*17*204
lim=Q(24*204,4**4)
assert ds==41616 and lim==Q(153,8)
spl={p:[leg(3,p),leg(17,p)] for p in (5,7,11,13,19)}
assert [p for p,v in spl.items() if v==[1,1]]==[13]
eps3=(2,1,0,0)
eps17=(3,0,2,0)
eps51=(50,-7,0,14)
epsX=(2,3,3,1)
assert all(norm(u)==1 for u in (eps3,eps17,eps51,epsX))
assert mul(epsX,epsX)==mul(eps3,eps51)
assert [x for x in range(1,9) if any(abs(x*x-17*y*y)==4 for y in (1,2))]==[8]
assert all(not any(x*x==1+51*y*y for x in range(1,51)) for y in range(1,7))
assert 50**2-51*7**2==1

print(json.dumps({"basis":["1","sqrt3","w","sqrt3*w"], "w":"(1+sqrt17)/2",
 "discriminant":ds,"Minkowski_bound":str(lim),
 "prime_minimal_norms":{"2":2,"3":9,"5":25,"7":49,"11":121,"13":13,"17":289,"19":361},
 "unramified_odd_symbols":spl,
 "principal_generators":{p:{"coefficients":x,"norm":norm(x)} for p,x in elts.items()},
 "unit_squares":{"epsilon3":eps3,"epsilon17":eps17,"epsilon51":eps51,
                 "extra":epsX,"extra_squared":mul(epsX,epsX)}}, sort_keys=True,indent=2))
