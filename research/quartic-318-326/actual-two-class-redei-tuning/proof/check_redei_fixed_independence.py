#!/usr/bin/env python3
"""Witness independence of two fixed rational squareclasses without expanding scales."""
from pathlib import Path
from hashlib import sha256
import json
root=Path(__file__).resolve().parent.parent
path=root/'linked-detector-twelve-compatible-incidences-r1'/'EXACT-TWELVE-INCIDENCES.json'
b=path.read_bytes(); assert sha256(b).hexdigest()=='b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744'
z=next(r for r in json.loads(b)['rows'] if r['prime']==4818481)
p=z['prime']; c=z['scales_mod_p2']
s=-32*pow(407*c[1]**2,-1,p)%p
t=pow(2399*c[2]**2,-1,p)%p
delta=(t-s)%p
assert delta==2532881 and pow(delta,(p-1)//2,p)==p-1
assert pow(2399,(p-1)//2,p)==1
print(json.dumps({'p':p,'s_residue':s,'t_residue':t,'delta_residue':delta,
                  'delta_sign':-1,'2399_sign':1},indent=2))
