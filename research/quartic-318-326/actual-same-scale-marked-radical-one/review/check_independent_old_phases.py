import hashlib
import json
from math import gcd
from pathlib import Path
import sys

# Reconstruct the exact S: columns are the old a and new same-c1 b factors,
# not the old cross-scale b factor and not changed local parameters.
assert len(sys.argv)==6
expected=(
    'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec',
    'd8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0',
    'b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744',
    '0d8a8a51bc89c1ba66dee18f22eb40ac51b2b681d227be212517915c7f535efc',
    '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
r=[]
origins=set()
for file,digest in zip(sys.argv[1:],expected):
    raw=Path(file).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==digest
    d=json.loads(raw)
    roots=d['rows']
    origins.add(d['literal_scalar_J'])
    r.extend(roots)
assert len(origins)==1
assert len(r)==len({x['prime'] for x in r})==16
v=[]
for x in r:
    p=x['prime']; q=p*p
    w=x['r_over_d_mod_p2']; c=x['scales_mod_p2'][1]
    c2w2=pow(w*c,2,q)
    a=(407*c2w2+32)%q; b=(2399*c2w2-1)%q
    ar=a*pow(407,-1,q)%q
    br=b*pow(2399,-1,q)%q
    assert (ar==p if p==415721 else ar%p!=0)
    assert br%p!=0
    chi=pow(br,(p-1)//2,p)
    assert chi in (1,p-1)
    v.append({'p':p,'a_factor_mod_p2':ar,'b_factor_mod_p2':br,'q1_norm_character':1 if chi==1 else -1,'q2_norm_character':1})
v_pa=next(x for x in v if x['p']==415721)
v_pb=next(x for x in v if x['p']==9807649)
assert v_pa['q1_norm_character']==v_pb['q1_norm_character']==-1
pilot=next(x for x in r if x['prime']==9807649)
orders=[x['order'] for x in pilot['arms']]
h=int(d['simultaneous_h_residue'])
L=int(d['simultaneous_h_modulus'])
assert orders==[2453441,29] and h%orders[0]==0 and h%orders[1]==1
assert L%orders[0]==L%orders[1]==0
assert pilot['assigned_scale']==2 and pilot['assigned_root_index']==3
pa,pb=415721,9807649
r_prim,r_op=[x['root'] for x in pilot['arms']]
assert r_prim==8296152 and r_op==pb-r_prim and pow(r_prim,2,pb)==2
x,y=pilot['AB']
assert (x,y)==(3057,680) and x*x+y*y==pb
N_plus,N_minus=[pb+1+s*2*x for s in (1,-1)]
assert [N_plus,N_minus]==[9813764,9801536] and gcd(N_plus,N_minus)==4
assert N_plus%orders[0]==N_minus%orders[1]==0
assert N_minus%orders[0]!=0 and N_plus%orders[1]!=0
print(json.dumps({'rows':v,'positive_pilot_old_scale':2,'positive_new_clones_scale':1,'positive_pilot_orders':orders,'positive_pilot_groups':[N_plus,N_minus]},indent=2))
