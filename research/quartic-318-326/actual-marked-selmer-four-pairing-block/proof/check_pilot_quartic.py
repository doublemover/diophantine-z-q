#!/usr/bin/env python3
import json
from math import isqrt

p=415721
assert all(p % d for d in range(2,isqrt(p)+1))
i=436*pow(475,-1,p)%p
assert i*i%p==p-1
rows=[]
for n, expected, expected_rs in [
    (1,1,(311792,119902)),
    (9,p-1,(311794,354458)),
]:
    u=2
    v=n*pow(u,-1,p)%p
    r=(u+v)*pow(2,-1,p)%p
    s=(u-v)*pow(2*i,-1,p)%p
    assert (r,s)==expected_rs
    assert ((r+i*s)%p,(r-i*s)%p)==(u,v)
    assert (r*r+s*s)%p==n
    assert pow(n,(p-1)//2,p)==1 and pow(n,(p-1)//4,p)==expected
    assert all(pow(j,4,p)!=1 for j in (u,v))
    rows.append(dict(i=i,norm=n,gaussian=[r,s],split=[u,v],quartic_sign=1 if expected==1 else -1))
print(json.dumps(dict(p=p,rows=rows),sort_keys=True))
