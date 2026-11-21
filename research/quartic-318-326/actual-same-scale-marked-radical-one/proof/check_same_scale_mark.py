#!/usr/bin/env python3
"""Replay actual local same-scale Selmer rows and all 16 unchanged balls.

Arguments: the exact triad, six, twelve, XIV, and XVI contact JSONs in order.
"""
from itertools import product
from math import prod, isqrt, gcd
from pathlib import Path
import hashlib, json, sys
pins = [
'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec',
'd8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0',
'b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744',
'0d8a8a51bc89c1ba66dee18f22eb40ac51b2b681d227be212517915c7f535efc',
'6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1',
]
assert len(sys.argv)==6
data=[]
for f,hash_ in zip(sys.argv[1:],pins):
    raw=Path(f).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==hash_
    data.append(json.loads(raw))
assert len({d['literal_scalar_J'] for d in data})==1
rows=[r for d in data for r in d['rows']]
assert len(rows)==len({r['prime'] for r in rows})==16
S=-32*407*2399**2
T=2399*407**2
PA=415721
PB=9807649
supports=[-1,2,5,7,11,37,2399,'pa','qa','q1']
T0,Ts,Tt=0b110,0b101,0b011
movs={'pa','qa','q1','q2'}
def fix(g):return PA if g in ('pa','qa') else PB if g in ('q1','q2') else g
def chi(g,p):
    if g in movs and p in movs:
        assert g!=p
        return int((g in ('pa','qa') and p=='q1') or (p in ('pa','qa') and g=='q1'))
    a,b=fix(g),fix(p)
    assert a%b
    z=pow(a%b,(b-1)//2,b)
    assert z in (1,b-1)
    return int(z==b-1)
def mulrow(vec,L):
    x=0
    for a,b in zip(vec,L):
        if b:x^=a
    return x
def c_odd(a,p):
    v=0
    while a%p==0:
        v^=1; a//=p
    return (v,chi(a,p))
def Ctuple(ds,p):
    r=[c_odd(d,p) for d in ds]
    return sum(e<<i for i,(e,_) in enumerate(r)),sum(u<<i for i,(_,u) in enumerate(r))
def tor_table(p):
    ret={(0,0)}
    for i,xi in enumerate([0,S,T]):
        r=[xi-xj for xj in [0,S,T]]
        r[i]=prod(y for j,y in enumerate(r) if i!=j)
        ret.add(Ctuple(r,p))
    assert len(set(v for v,u in ret))==4
    return ret
loc={p:tor_table(p) for p in [11,37,2399]}
C_A={0:0,T0:T0,Ts:Tt,Tt:Ts}
C_B={0:0,T0:Tt,Ts:Tt,Tt:0}
local_chars={p:[0 if p==g else chi(g,p) for g in supports] for p in [5,7,11,37,2399,'pa','qa','q1','q2']}
# F2 norm parity at 2: characters from generators 5,7 etc; v2 separately.
u2=[fix(g)%8 if g!=2 else 1 for g in supports]
ends=[]
support_val=[(0,Ts),(0,Tt),(0,T0),(0,T0)]+[(0,T0,Ts,Tt)]*6
assert len(support_val)==len(supports)
for V in product(*support_val):
    if V[1]&4:continue
    v=1
    for g,C in zip(u2,V):
        if C&4:v=v*g%8
    if v!=1:continue
    ok=True
    for p,L in local_chars.items():
        i=supports.index(p) if p!='q2' else None
        v=V[i] if i is not None else 0
        u=mulrow(V,L)
        if p==5:
            cond=(v&1)==0 and not u&1
        elif p==7:
            cond=(u&1)==(v!=0)
        elif p in loc:
            cond=(v,u) in loc[p]
        elif p in ('pa','qa'):
            cond=C_A[v]==u
        elif p=='q1':
            cond=C_B[v]==u
        else:
            cond=u==0
        if not cond:
            ok=False;break
    if ok: ends.append(V)

assert len(ends)==8
mark=(0,0,0,T0,T0,T0,Tt,T0,T0,0)
u=(0,0,0,0,0,0,Tt,Ts,Ts,Tt)
v=(0,0,T0,0,Ts,0,T0,0,0,0)
gens=[mark,u,v]
assert set(ends)=={tuple(mulrow(column,b) for column in zip(*gens))
                   for b in product((0,1),repeat=3)}
assert 407+32*2399==3**2*5**2*7**3
assert S%32==0 and S//32%8==1 and T%8==7
assert c_odd(-407,11)[0]==1
assert [chi(a,p) for p in [PA,PB] for a in [-814,2399,7*11*37*2399]]==[0,0,1,1,0,0]
assert all(all(p%d for d in range(2,isqrt(p)+1)) for p in [PA,PB])
phase=[]
for r in rows:
    p=r['prime'];pp=p*p
    assert p%8==1 and p>76176
    c=r['scales_mod_p2'][1]; w=r['r_over_d_mod_p2']
    nv=(c*w)**2%pp
    old_a=(nv+32*pow(407,-1,pp))%pp
    new_t=(nv-pow(2399,-1,pp))%pp
    assert old_a==p if p==PA else old_a%p!=0
    assert new_t%p!=0
    eps=chi(new_t,p)
    if p==PA: assert eps==1
    phase.append([p,old_a,new_t,eps])
a=next(r for r in rows if r['prime']==PB)
assert a['assigned_scale']==2 and a['assigned_root_index']==3
assert [j['order'] for j in a['arms']]==[2453441,29]
h,L=map(int,(data[-1]['simultaneous_h_residue'],data[-1]['simultaneous_h_modulus']))
assert h%2453441==0 and h%29==1 and L%(2453441*29)==0
def weil(a,b):return (a!=0 and b!=0 and a!=b)*1
trans=[]
for g in ['pa',11,2399]:
    x,y,z=[c[supports.index(g)] for c in gens]
    trans.append([g,[x,y,z],[weil(x,y),weil(x,z),weil(y,z)]])
assert [r[2] for r in trans]==[[1,0,0],[0,1,0],[0,1,1]]
print(json.dumps({'roots':[0,S,T],'support_labels':supports,
    'all_inherited_phase_rows':phase,'odd_fixed_torsion_tables':
    {p:sorted(a) for p,a in loc.items()},'fixed_and_moving_unit_bits':local_chars,
    'same_scale_basis':gens,'all_normalized_classes':ends,
    'normalized_dimension':3,'inertia_square_controls':trans},indent=2))
