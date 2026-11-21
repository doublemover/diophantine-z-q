#!/usr/bin/env python3
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
base=Path(__file__).resolve().parent.parent
def pin(path, h):
    b=(base/path).read_bytes()
    assert sha256(b).hexdigest()==h
    return json.loads(b)
j=pin('linked-detector-gaussian-order29-new-classes-r1/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json',
      '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
k=pin('linked-detector-two-class-fixed-selmer-quotient-r1/EXACT-FIXED-QUOTIENT-KNOWN-ROWS.json',
      '9bde7b622ef30b2528979ed684da927b12b8c5e0eecf38ea20461149c1059662')
L=int(j['simultaneous_h_modulus'])
p=2399
counts=[(475+sgn)**2+436**2 for sgn in (1,-1)]
assert L%p==221 and [u%p for u in counts]==[1645,2144]
assert 475**2+436**2==415721
rs={r['p']:r['ratio_mod_p2'] for r in k['anchor_ratio_rows']}
assert all(rs[q]%q for q in (11,37,2399))
assert rs[3]==6 and p%3==2 and 814%3==1 and 407%8==7
# Basis (T_s,T_t), v=(v,0) by real test; form of J without assuming self-adjoint.
A=[]
for u,b,c,d,v in product(range(2),repeat=5):
    if u!=d or c!=0 or b!=v:continue
    A.append((u,b,c,d,v))
assert A==[(u,w,0,u,w) for u,w in product(range(2),repeat=2)]
print(json.dumps({'L_mod_2399':L%p,'first_Gaussian_counts':counts,
                  'counts_mod_2399':[u%p for u in counts], 'rho_3':rs[3],
                  'fixed_ratio_unit_residues':{q:rs[q]%q for q in (11,37,p)},
                  'P_mod_8':407%8,'local_self_adjoint_and_sign_options':A},indent=2))
