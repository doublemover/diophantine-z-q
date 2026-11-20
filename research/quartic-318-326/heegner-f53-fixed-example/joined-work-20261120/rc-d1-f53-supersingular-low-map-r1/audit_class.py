#!/usr/bin/env python3
"""Read-only independent audit of one complete 288-row signed low class."""
from collections import Counter
from pathlib import Path
from hashlib import sha256
import json
import sys
from lookup import K, on_ell

def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P; u,v=Q
    if x==u and not(y+v):return None
    m=(3*x*x-4*x-3)/(2*y) if x==u else (v-y)/(u-x)
    X=m*m+2-x-u
    R=X,m*(x-X)-y
    assert on_ell(R)
    return R

def mul(m,P):
    Q=None
    while m:
        if m&1:Q=add(Q,P)
        P=add(P,P);m//=2
    return Q

def dump(R):
    return None if R is None else [x.j() for x in R]

def audit(src):
    tab_src=Path(__file__).with_name('LOW-48-SUPERSINGULAR-F53.json').read_bytes()
    records=json.loads(tab_src)['records']
    tab={tuple(rec['T']+rec['U']):rec['rows'][0]['phi'] for rec in records}
    assert len(tab)==len(records)==416
    raw=src.read_bytes()
    supplied=json.loads(raw)
    rows=supplied['rows']
    assert sorted((r['a17'],r['a19']) for r in rows)==[(i,j) for i in range(1,17) for j in range(1,19)]
    seen=Counter();S=None
    for row in rows:
        k=tuple(row['t16'][0]+row['t16'][1])
        assert tab[k]==row['phi']
        seen[k]+=1
        a,b=row['a17'],row['a19']
        sg=(1 if pow(a,8,17)==1 else -1)*(1 if pow(b,9,19)==1 else -1)
        assert sg==row['w']
        X,Y=(K(*a) for a in row['phi'])
        S=add(S,(X,sg*Y))
    R=mul(224,S)
    if 'raw_weighted_sum' in supplied:
        assert dump(S)==supplied['raw_weighted_sum']
    if 'additional_raw_order13_test' in supplied:
        assert dump(R)==supplied['additional_raw_order13_test']
    return dict(input_sha256=sha256(raw).hexdigest(),lookups_sha256=sha256(tab_src).hexdigest(),
                matching_signed_rows=len(rows),distinct_low_addresses=len(seen),
                multiplicities=sorted(Counter(seen.values()).items()),raw_weighted_sum=dump(S),
                raw_13_primary_projection=dump(R),projection_killed_by_13=mul(13,R) is None)
if __name__=='__main__':
    print(json.dumps(audit(Path(sys.argv[1])),sort_keys=True,indent=2))
