#!/usr/bin/env python3
"""Literal contacts and independent local division obstructions."""
import json
from math import prod

b = (0, 32, 76832, -343)
c = (-14,-6,42,-21)
assert len(set(b)) == 4
local = {}
for p,d in ((5,-1),(7,-3)):
    roots = [x for x in range(p) if (x*x-d) % p == 0]
    assert roots == [2,p-2]
    local[str(p)] = roots
out = {}
for p in (13,17,23,29,41):
    rows = []
    for t in range(p):
        if not prod(t-z for z in b) % p:
            continue
        n = [sum((x*x-co*(t-z))%p == 0 for x in range(p))
             for z,co in zip(b,c)]
        assert prod(n) in (0,16)
        rows.append((t,prod(n)))
    out[str(p)] = rows
print(json.dumps(dict(contacts=b, twists=c, splitting_roots=local,
                      finite_fibers=out),indent=2,sort_keys=True))
