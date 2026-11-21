#!/usr/bin/env python3
"""Exact symbolic local Kummer table on the two literal pilot classes."""
from pathlib import Path
from hashlib import sha256
from itertools import product
import json
src=Path(__file__).resolve().parent.parent/'linked-detector-gaussian-order29-new-classes-r1'/'EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json'
b=src.read_bytes()
assert sha256(b).hexdigest()=='6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1'
old=json.loads(b)
even=[v for v in product(range(2),repeat=3) if sum(v)%2==0]
Z=(0,0,0); T_b=(1,1,0)
def character(z,p):
    r=pow(z%p,(p-1)//2,p)
    assert r in (1,p-1)
    return 1 if r==1 else -1
def rows_for(p,s,first):
    W=[]
    for A,B in product(even,repeat=2):
        # Let eps=(sigma_current/p / p) be either sign of the
        # stripped unit. Opposite sigma is a unit square.
        tag=A if first else B
        ok=[]
        for eps in (1,-1):
            lhs=tuple((n,eps**n) for n in tag)
            rhs=[((0,1),)*3]
            for i in range(3):
                cs=[character(s[i]-s[j],p)for j in range(3) if j!=i]
                rhs.append(tuple((0,cs[0]*cs[1]) if j==i
                                 else (1,eps*character(s[i]-s[j],p))
                                 for j in range(3)))
            ok.append(lhs in rhs)
        assert ok[0]==ok[1]
        if ok[0]:W.append((A,B))
    return W
R=[]
for i,row in enumerate(old['rows']):
    p=row['prime']; c=row['scales_mod_p2']
    assert (p,row['assigned_scale'],row['assigned_root_index'])==[(415721,1,4),(9807649,2,3)][i]
    assert p%8==1
    sa=-32*pow(407*c[1]**2,-1,p)%p
    sb=pow(2399*c[2]**2,-1,p)%p
    b=[character(x,p)for x in (sa,sb,sa-sb)]
    assert b==[[1,1,1],[-1,1,1]][i]
    W=rows_for(p,[0,sa,sb],i==0)
    assert W==[(A,B)for A,B in product(even,repeat=2) if i==0 or B in (Z,T_b)]
    R.append({'p':p,'literal_residues':[sa,sb,(sa-sb)%p],'Legendre_bits':b,
              'pair_supported_Kummer_tuples':W})
assert len(R[1]['pair_supported_Kummer_tuples'])==8
print(json.dumps({'root_order':['0','D*s_a','D*s_b'],'pilot_rows':R,
                  'pair_supported_Sel2_dimension':3,'torsion_Kummer_dimension':2,
                  'Sel2_dimension_lower_bound':5},indent=2))
