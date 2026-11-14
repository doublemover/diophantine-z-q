#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def pack(x):return ((x[0],x[1]),((x[2],x[3]),x[4]))
def unpack(x):return (x[0][0],x[0][1],x[1][0][0],x[1][0][1],x[1][1])
def frac(x):return x-x.numerator//x.denominator
def tent(x):return max(F(0),1-abs(x))
def period(x):
    out=F(1)
    for a in x:out*=sum((tent(a+n) for n in range(-6,7)),F(0))
    return out
zs=(1,-1,2,0,-2);freq=(3,-2,1,4,-1);n=0
for x in product([F(0),F(1,3),F(-1,2),F(7,4)],repeat=5):
    assert unpack(pack(x))==x
    y=tuple(a+b for a,b in zip(x,zs))
    assert tuple(map(frac,x))==tuple(map(frac,y))
    assert period(x)==period(y)==1
    assert sum(a*b for a,b in zip(freq,y))-sum(a*b for a,b in zip(freq,x))==sum(a*b for a,b in zip(freq,zs))
    n+=1
out={'status':'PASS','rational_points':n,'checks':['literal2+2+1 pack inverse','all-coordinate integer quotient fibers','actual compact continuous separable tent periodization descends','integer-frequency character difference is integral'],'volume_convention':'same five real coordinate factors, unit box volume1; no Euclidean scaling','scope':'Finite rational regression only, not continuity, measure transport, or Lean certification.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',n,'exact torus/periodization regressions')
