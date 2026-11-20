#!/usr/bin/env python3
"""Arithmetic bounds for the literal denominator-29 direct CM4 enumerator."""
from math import isqrt
import json
n=2811626664334219040035976315
assert n==204618888056724185*114649*119851
theta_lower=7117846043391004196808870789
T=lambda d:3*29**2*16*d
def intervals(d):
    t=T(d)
    h=isqrt(t)
    residues=[r for r in range(212) if (t-r*r)%212==0]
    return t,h,residues,sum((h-r)//212+1 for r in residues),isqrt(t//212)
t,h,residues,exact,cap=intervals(n)
tb,hb,_,_,capb=intervals(n*theta_lower)
# On the valid ray t=0 mod4 and t is a nonzero square mod53 since
# (-d/53)=- and (3/53)=-. Thus there are exactly four phases mod212.
# For any four roots the count is at least 4*floor(sqrt(t)/212).
assert exact==201_011_809_760_446 and cap==731_694_032_049_598
assert 4*(hb//212)==16_958_829_297_287_827_009_030_020_160
print(json.dumps(dict(actual_base_n=n,actual_theta_lower=theta_lower,base_T=t,
         base_exact_four_residue_phases=residues,base_exact_slice_count=exact,
         base_prime_sieve_array_cap=cap,companion_T_lower=tb,
         companion_slice_count_lower=4*(hb//212),companion_prime_sieve_array_cap_lower=capb),indent=2))
