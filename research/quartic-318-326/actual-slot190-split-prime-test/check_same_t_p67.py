#!/usr/bin/env python3
import json,sys
from math import gcd,isqrt
from pathlib import Path
D=json.loads(Path(sys.argv[1]).read_text())
r,d=D['test_contact_numroot'],D['test_contact_denroot']
p=67
assert all(p%q for q in range(2,isqrt(p)+1))
u,v=r*r,d*d
a=tuple(g%(p*p) for g in (u,2*u+v,u+v,2399*u-v,407*u+32*v))
assert a==(1396,4007,2611,3484,1037)
assert [i for i,g in enumerate(a) if g%p==0]==[3] and a[3]==52*p
assert gcd(2*2399*407*d,p)==1 and (u-v)%p==47
assert pow(2,(p-1)//2,p)==p-1
print("The displayed t has an isolated simple inert contact at 67.")
