#!/usr/bin/env python3
"""Exact rational interval for the normalized primitive-period value.

The paper gives the integral-period lattice, not this interval alone.
Input L-value enclosure is the exact pinned earlier interval packet.
Every printed rational endpoint proof uses Fraction, not a numerical period.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math
from certify_companion_value import atan_bounds

def main():
    src=Path(__file__).resolve().parent/'COMPANION-CENTRAL-INTERVAL.json'
    b=src.read_bytes()
    h=hashlib.sha256(b).hexdigest()
    assert h=='16166f7f30dbdc04635824dbb96891acc3c295e46e3ab3892229e68ea9327dd6'
    data=json.loads(b)
    assert data['fundamental_twist']==146965
    LL,LU=map(F.from_float,data['central_value_interval'])
    a,b=atan_bounds(5,20);c,d=atan_bounds(239,8)
    piL,piU=16*a-4*d,16*b-4*c
    n=16
    k=sum((F(math.comb(2*j,j)**2,64**j) for j in range(n)),F(0))
    e=F(1,4**n)/F(3,4)
    loK,hiK=piL*k/2,piU*(k+e)/2
    T=10**30; sn=math.isqrt(146965*T*T)
    sL,sU=F(sn,T),F(sn+1,T)
    assert sL*sL<146965<sU*sU
    rL,rU=sL*LL/hiK,sU*LU/loK
    assert F(204799,100)<rL<2048<rU<F(204801,100)
    assert F(2047)<rL and rU<F(2049)
    rr=lambda a:[str(a.numerator),str(a.denominator)]
    print(json.dumps(dict(prior_interval_sha256=h,
            prim_real_period_enclosure=[rr(loK),rr(hiK)],
            sqrt146965_enclosure=[rr(sL),rr(sU)],
            normalized_ratio_enclosure=[rr(rL),rr(rU)],
            coarse_rational_interval=['204799/100','204801/100'],
            only_integer_in_coarse_interval=2048,
            exact_integer_v2=11),indent=2))
if __name__=='__main__':main()
