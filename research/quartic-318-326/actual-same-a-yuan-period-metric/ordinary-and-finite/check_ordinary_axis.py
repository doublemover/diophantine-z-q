#!/usr/bin/env python3
"""Independent finite correction test (not actual QM finite place data)."""
import json

contacts = (0,32,76832,-343)
twists = (-14,-6,42,-21)
rows = {}
for p in (13,17,23,29,41):
    mod = p*p
    hits = 0
    for b,c in zip(contacts,twists):
        for q in range(p):
            for x in range(1,p):
                if (x*x-c*(q-b))%p:
                    continue
                for j in (0,1,3):
                    tq = q+p*j
                    rhs = c*(tq-b)
                    d = ((rhs-x*x)*pow(2*x, -1, mod))%mod
                    assert d%p == 0
                    target = (x+d)%mod
                    rs = [x+p*k for k in range(p) if ((x+p*k)**2-rhs)%mod == 0]
                    assert rs == [target]
                    # Varying t by p once changes the root by p times
                    # the derivative in its same unit branch.
                    t1 = tq+p
                    e = ((c*(t1-b)-target**2)*pow(2*target,-1,mod))%mod
                    assert e == p*((c*pow(2*x,-1,p))%p)
                    hits += 1
    rows[str(p)] = hits
print(json.dumps({'contacts': contacts,'twists': twists,'hits': rows,'total': sum(rows.values())},
                 indent=2,sort_keys=True))
