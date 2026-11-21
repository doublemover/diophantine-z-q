#!/usr/bin/env python3
"""Actual weight-zero Hecke trace separates six prior marked scalar aliases."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

DONOR="1bedcf9672b3f128f5549e53cbb32430e4d45fb000f840aba4e32826b6d5ecaa"
FULL="08e19a0491820957ef79f5c4e72b582a5ec3052cad658110deec7599d910e8bf"
PAIR=[(521,1601),(769,2129),(847,1768),(902,1594),(1125,1239),(1370,1407)]

def checked(p,h):
    p=Path(p)
    assert hashlib.sha256(p.read_bytes()).hexdigest()==h
    return p

p=checked(sys.argv[1],DONOR)
f=checked(sys.argv[2],FULL)
old=json.loads(f.read_bytes())
assert old["different_W_orbit_aliases"]==[list(ij) for ij in PAIR]
assert old["actual_W_orbits"]==2400 and old["all_character_tuples"]==2394
s=importlib.util.spec_from_file_location("atkin_donor",p)
m=importlib.util.module_from_spec(s); s.loader.exec_module(m)
_,fixed,_=m.initial()
tables=m.build()
q=23
assert q not in (13,*m.PS)
m.MF[q]=m.mat(q)
assert m.det4(m.MF[q])%q
arrows={}
for u in m.nm(q):
    K=m.kernel(m.act(u,q),q)
    assert K not in arrows
    arrows[K]=(u,tuple(m.act(u,l) for l in m.PS))
assert sorted(arrows)==list(range(q+1))

def trace(j):
    X=fixed[:-1]+(j,)
    weights=[]
    for k,(_,A) in sorted(arrows.items()):
        Y=tuple(m.moved(B,l,t) for B,l,t in zip(A,m.PS,X))
        ds,_,_=m.evaluate(Y,tables)
        _,U,_=m.invariants(ds)
        val=tuple(m.a(U[b],m.pw(U[b],13))[0] for b in (127,126))
        weights.append((k,val))
    one=sum(v[0] for _,v in weights)%13
    two=sum(v[1] for _,v in weights)%13
    return dict(line=j,first=one,second=two,trace_sum=(one+two)%13,
                outgoing_weight0_values=weights)

rows=[[trace(j),trace(k)] for j,k in PAIR]
assert [(a["trace_sum"],b["trace_sum"]) for a,b in rows]==[(7,8),(8,5),(8,9),(0,10),(9,6),(11,4)]
print(json.dumps(dict(prime=q,residue_prime=13,negative_masks=[127,126],
                      old_W_orbits=2400,new_distinct_combined_scalar_tuples=2400,
                      six_pair_certificates=rows),indent=2,sort_keys=True))
