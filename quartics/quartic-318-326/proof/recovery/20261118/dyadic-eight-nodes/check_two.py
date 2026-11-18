#!/usr/bin/env python3
from pathlib import Path
import itertools, re
f=Path(__file__).with_name('inputs')/'OriginalIntegerAffineModel318.lean'
c=list(map(int,re.search(r'def contacts : Fin 4 → ℤ := !\[([^\]]+)\]',f.read_text())[1].split(',')))
assert c==[0,4*8,4*19208,-343]
assert (343-1)//2==171 and c[2]-c[1]==4*19200
finite=[(u,h,k,w) for u,h,k,w in itertools.product(range(2),repeat=4) if (h*h+u*h)%2==(k*k+u*k)%2==w%2==0]
infty=[(x,h,k,w) for x,h,k,w in itertools.product(range(2),repeat=4) if x==0 and (h*h+h)%2==(k*k+k)%2==w%2==0]
assert len(finite)==5 and len(infty)==4 and len([q for q in finite if q[0]==1])==4
print('PASS: integer constants, 5 finite and 4 boundary residue labels, 8 simple marked centers, 1 residual')
