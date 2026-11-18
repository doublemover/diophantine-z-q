#!/usr/bin/env python3
"""Finite independent arithmetic checks, not a point-count proof of regularity."""
from pathlib import Path
import re,itertools
p=Path(__file__).with_name('inputs')/'OriginalIntegerAffineModel318.lean'
c=list(map(int,re.search(r'def contacts : Fin 4 → ℤ := !\[([^\]]+)\]',p.read_text())[1].split(',')))
assert c==[0,32,76832,-343] and [v%5 for v in c]==[0,2,2,2]
assert c[1]-c[2]==-3072*5**2 and c[1]-c[3]==15*5**2
assert {-3072%5,32%5}=={3,2} and 15%25!=0
assert not any(y*y%5==2 for y in range(5))
# Actual quadratic extension b^2=2; verify all 25-field rational exceptional
# pi-chart directions split into exactly the two covered residue cases.
F=list(itertools.product(range(5),repeat=2))
sq=lambda z: ((z[0]**2+2*z[1]**2)%5,2*z[0]*z[1]%5)
directions=[(U,V,W) for U,V,W in itertools.product(F,repeat=3)
 if (sq(V)[0]-sq(U)[0])%5==(-3072)%5 and sq(V)[1]==sq(U)[1] and sq(W)==sq(U)]
assert directions and all((u!=(0,0) and w!=(0,0)) or
    (u==(0,0) and w==(0,0) and v!=(0,0)) for u,v,w in directions)
assert any(v==(0,0) for _,v,_ in directions)
print(f'PASS: exact contacts, first blowup constants, F25 center, {len(directions)} arithmetic chart directions with labels, including V=0')
