#!/usr/bin/env python3
"""Check the literal pilot point counts and all finite reciprocal-phase residues."""
from pathlib import Path
from hashlib import sha256
from math import gcd, isqrt
import json
root=Path(__file__).resolve().parent.parent
spec=[
('linked-detector-three-scale-incidence-r1','EXACT-THREE-SCALE-INCIDENCE.json','a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec'),
('linked-detector-six-compatible-incidences-r1','EXACT-SIX-INCIDENCES.json','d8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0'),
('linked-detector-twelve-compatible-incidences-r1','EXACT-TWELVE-INCIDENCES.json','b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744'),
('linked-detector-low-opposite-unhit-r1','EXACT-LOW-OPPOSITE-NEW-CLASS.json','0d8a8a51bc89c1ba66dee18f22eb40ac51b2b681d227be212517915c7f535efc'),
('linked-detector-gaussian-order29-new-classes-r1','EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json','6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')]
data=[]
for d,f,h in spec:
    b=(root/d/f).read_bytes()
    assert sha256(b).hexdigest()==h
    data.append(json.loads(b))
assert len({j['literal_scalar_J']for j in data})==1
rows=[r for j in data for r in j['rows']]
assert len(rows)==len({r['prime']for r in rows})==16
h,L=map(int,(data[-1]['simultaneous_h_residue'],data[-1]['simultaneous_h_modulus']))
assert h%2==L%2==0
p0=415721
z=next(r for r in rows if r['prime']==p0)
assert all(p0%d for d in range(2,isqrt(p0)+1))
assert z['assigned_scale']==1 and z['assigned_root_index']==4
a,b=z['AB']; assert (a,b)==(475,436) and a*a+b*b==p0
assert p0%7==5 and pow(p0,3,7)==6 and p0%8==1
def count(p,r):
    d=(3-r)%p; assert d
    w=[0]*p
    for y in range(p):w[y*y%p]+=1
    return 1+sum(w[x*(x*x-d*d)%p]for x in range(p))
C=[count(p0,r['root'])for r in z['arms']]
N=[r['order']for r in z['arms']]
assert C==[414772,416672] and gcd(*C)==4 and C==[p0+1-2*a,p0+1+2*a]
assert N==[103693,29] and h%N[0]==0 and h%N[1]==1 and h%p0**4==p0**3
def chi(n,p):
    s=pow(n%p,(p-1)//2,p)
    return 0 if s==0 else (1 if s==1 else -1)
S=[]
for k in rows:
    p=k['prime']; pp=p*p
    assert p%8==1 and p>76176
    A,B=k['AB']; assert A*A+B*B==p
    i=A*pow(B,-1,p)%p; assert i*i%p==p-1
    c=k['scales_mod_p2'][1]; w=k['r_over_d_mod_p2']
    A=(c*c*w*w+32*pow(407,-1,pp))%pp
    if p==p0:
        assert A==p
        num,K=A//p,1
    else:
        assert A%p
        num,K=A,p0
    eta=chi(num*K,p); assert eta
    u=2
    v=next(v for v in range(2,p) if pow(v,4,p)!=1 and chi(u*v,p)==eta)
    assert pow(u,4,p)!=1
    re=(u+v)*pow(2,-1,p)%p;im=(u-v)*pow(2*i,-1,p)%p
    assert (re+im*i)%p==u and (re-im*i)%p==v
    for s in (1,-1,i,-i):
        assert all((s*u+t)%p for t in (1,-1))
        assert all((s*v+t)%p for t in (1,-1))
    assert chi(re*re+im*im,p)==eta
    S.append({'p':p,'stripped_target_factor':num,'strip_K':K,
              'required_q_character':eta,'i':i,'residue_coordinates':[re,im],
              'split_unit_coordinates':[u,v]})
print(json.dumps({'pilot_prime':p0,'oriented_counts':C,'oriented_orders':N,
                  'odd_arm_group_gcd':gcd(*C)//4,
                  'literal_slot':241,'theta':[-32,407],
                  'all_inherited_contact_symbol_residues':S},indent=2))
