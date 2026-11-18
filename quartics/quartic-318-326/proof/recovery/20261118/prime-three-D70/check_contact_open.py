#!/usr/bin/env python3
"""Verify finite arithmetic witnesses, not scheme-theoretic or Lean claims."""
from itertools import permutations
from pathlib import Path
import re
c = [0, 32, 76832, -343]
source = Path(__file__).with_name("inputs") / "OriginalIntegerAffineModel318.lean"
m = re.search(r'def contacts : Fin 4 → ℤ := !\[([^\]]+)\]',source.read_text())
assert m and [int(v) for v in m[1].split(",")]==c
pairs=[]
for i,j in permutations(range(4),2):
    d=c[i]-c[j]
    for n in (9*70**10,(c[i]-2)**2*70**10):
        q,r=divmod(n,d)
        assert not r and q*d==n
    pairs.append((i,j,d))
assert len(pairs)==12
assert [v%3 for v in c]==[0,2,2,2]
assert all(x*x%3!=2 for x in range(3))
assert all((a*b)%3!=0 for a in (1,2) for b in (1,2))
# The unsquared witness for the last pair would give a false certificate.
assert ((c[2]-2)*70**10)%(c[2]-c[3]) != 0
print("PASS: source constants, 24 divisibilities, char-3 residues, F3 nonsquare, negative control")
