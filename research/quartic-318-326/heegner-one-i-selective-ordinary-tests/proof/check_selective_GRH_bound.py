#!/usr/bin/env python3
"""Exact use of Grenié–Molteni's constant 4 clause on the actual mirror."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent.parent/"actual-one-I-mirror-even-tower-r1/EXACT-MIRROR-EVEN-TOWER-AND-CHARTS.json"
x=p.read_bytes();assert hashlib.sha256(x).hexdigest()=="962cc16a0b4a09cb9469dfd286bec9976b51aeca6ac7ecf6c77a255aafc505d0"
j=json.loads(x);d=j["d"]
assert j["field_discriminants"]["full"]==2**266*3**144*13**167*d**84
def series(x,n=24):
    assert 1<=x<=2
    t=(x-1)/(x+1)
    a=sum(2*t**(2*k+1)/(2*k+1) for k in range(n))
    b=2*t**(2*n+1)/((2*n+1)*(1-t*t))
    return a,a+b
ln2=series(F(2))
def ln(x):
    k=x.bit_length()-1
    z=series(F(x,2**k))
    return tuple(a+k*b for a,b in zip(z,ln2))
lo=hi=F(0)
for x,k in [(2,266),(3,144),(13,167),(d,84)]:
    a,b=ln(x);lo+=k*a;hi+=k*b
assert 0<lo<hi<6100<F(6**168,3)
L=4*lo*lo;H=4*hi*hi
floor=L.numerator//L.denominator
assert H<floor+1
assert 1951**3>50*floor and 5303**2<floor
print(json.dumps(dict(d=d,requires_GRH=True,
    exact_floor_of_4_log_disc_squared=floor,
    least_safe_good_split_norm=1951**3,
    degree_2_q5303_norm=5303**2,
    no_rank_claim=True),indent=2,sort_keys=True))
