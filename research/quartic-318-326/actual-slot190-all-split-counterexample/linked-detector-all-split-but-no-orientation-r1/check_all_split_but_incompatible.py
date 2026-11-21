#!/usr/bin/env python3
from math import gcd, isqrt, prod
from pathlib import Path
from hashlib import sha256
import json,runpy
det=Path(__file__).resolve().parent.parent/'linked-detector-square-den2399-r1'/'check_actual_2399_square_denominator.py'
assert sha256(det.read_bytes()).hexdigest()=='a3697d5d857a1b4c48dd5b8bda7d83604842e8cb597818076419b1b16f14c347'
local_order_data=runpy.run_path(str(det))['local_order_data']
certs={
1506259129: {2:3,3:1,11:1,5705527:1},
5705527: {2:1,3:1,950921:1},
950921: {2:3,5:1,23773:1},
23773: {2:2,3:1,7:1,283:1},
1573893649: {2:4,3:2,10929817:1},
10929817: {2:3,3:4,101:1,167:1},
11052154848503: {2:1,23:1,353:1,680635229:1},
680635229: {2:2,7:1,13:1,23:1,81299:1},
81299: {2:1,7:1,5807:1},
5807: {2:1,2903:1},
10998934699633: {2:4,3:1,11:1,61:1,3889:1,87811:1},
87811: {2:1,3:1,5:1,2927:1},
253537: {2:5,3:1,19:1,139:1},
}
witness={}
def prime(p):
    if p<5000: assert p>=2 and all(p%d for d in range(2,isqrt(p)+1))
    elif p not in witness:
        D=certs[p]
        assert prod(q**m for q,m in D.items())==p-1
        for q in D: prime(q)
        a=next(k for k in range(2,100) if pow(k,p-1,p)==1 and
               all(gcd(pow(k,(p-1)//q,p)-1,p)==1 for q in D))
        witness[p]=a

m,n=40783,12210
assert gcd(m,n)==1 and (m-n)%2==1
r,d,s=m*m-n*n,2*m*n,m*m+n*n
assert gcd(r,d)==1 and r*r+d*d==s*s and r*r>2*d*d
assert d%(4*3*5*17*407*2399)==0
u,v=r*r,d*d
G=[u,2*u+v,u+v,2399*u-v,407*u+32*v]
factors=[(253537,10998934699633),(433,479,11052154848503),(1573893649,1506259129)]
P=[p for F in factors for p in F]
assert len(set(P))==len(P)
for C,F,g in zip((2,2399,407),factors,(G[1],G[3],G[4])):
    assert C*prod(F)==g
for p in P:
    prime(p)
    assert p%8 in (1,7) and pow(2,(p-1)//2,p)==1 and d%p!=0
p=479
assert G[3]%p==0 and G[3]%(p*p)!=0 and all(G[i]%p for i in (0,1,2,4))
assert (u-v)%p and gcd(d*2*2399*407,p)==1
rows=local_order_data(p)
cross=[gcd(a['primary_modulus'],b['opposite_modulus']) for a,b in (rows,rows[::-1])]
assert [a['order']for a in rows]==[240,120] and cross==[120,60]
print(json.dumps({'m':m,'n':n,'r':r,'d':d,'s':s,'contact_numerators':G,
                  'exact_factors_G1_over2_G3_over2399_G4_over407':factors,
                  'rational_contact_odd_support':sorted(P),
                  'p_minus_one_factor_certificates':certs,'prime_witnesses':witness,
                  'target_p':p,'G_residues_mod_p2':[g%(p*p)for g in G],
                  'Delta_numerator_mod_p':(u-v)%p,'actual_order_rows':rows,'cross_gcds':cross},indent=2))
