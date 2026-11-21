#!/usr/bin/env python3
"""Exact extra escape-5 check using only G1 and G4."""
from itertools import combinations
from math import prod, isqrt
from pathlib import Path
import hashlib, json
p=Path(__file__).resolve().parent.parent/'linked-detector-finite-saturation-r1'/'EXACT-FINITE-CONTACT-ESCAPE-CONTROLS.json'
d=p.read_bytes()
assert hashlib.sha256(d).hexdigest()=='4d9d6bccd5d68479695bc2ffc6af251a8c746f8f389ac5c8a53e4f52fbf46ff9'
fixed=json.loads(d)
U=sorted({5,*(r[0] for r in fixed['wide_free_prime_fourth_form_rows'])})
assert len(U)==16 and all(all(p%d for d in range(2,isqrt(p)+1)) for p in U)

def chi(n,p):
    v=pow(n%p,(p-1)//2,p)
    return 0 if v==0 else 1 if v==1 else -1

P4=[p for p in U if chi(-32*407,p)==1]
P1=[p for p in U if chi(-2,p)==1]
assert [p for p in P4 if p%3==2]==[5]
assert P1==[11,131,163,1489,1041427]
assert chi(-2,5)==-1 and chi(-1,5)==1
classes=[]
for n in range(len(P1)+1):
    for s in combinations(P1,n):
        v=prod(s)
        if v%24==1 and chi(v,17)==1:
            classes.append([list(s),v,v%5,chi(2*v,5)])
assert sorted(v[1] for v in classes)==[1,1441,169752601,244613498041]
assert all(a==1 and b==-1 for _,_,a,b in classes)
print(json.dumps(dict(actual_h=fixed['actual_h'],omitted_primes=U,
                      G4_possible_odd_factors=P4, G4_only_2_mod_3_factor=[5],
                      G1_possible_extra_odd_factors=P1,G1_admitted_classes=classes),
                 indent=2))
