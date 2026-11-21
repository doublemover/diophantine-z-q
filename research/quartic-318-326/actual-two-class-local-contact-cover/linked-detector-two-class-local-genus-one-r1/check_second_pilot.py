#!/usr/bin/env python3
"""Direct second-pilot finite group counts, reusing only exact XVI rows."""
from pathlib import Path
from hashlib import sha256
from math import gcd, isqrt
import json
root=Path(__file__).resolve().parent.parent
s=(root/'linked-detector-gaussian-order29-new-classes-r1'/'EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json').read_bytes()
assert sha256(s).hexdigest()=='6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1'
D=json.loads(s)
p=9807649; pp=p*p
assert all(p%d for d in range(2,isqrt(p)+1))
K=next(z for z in D['rows'] if z['prime']==p)
assert K['assigned_scale']==2 and K['assigned_root_index']==3 and p%8==1 and pow(p,3,7)==6
assert K['T_j_mod_p2'][2]==(pow(2399,-1,pp)+p)%pp
# Square-residue truth table and symmetry x -> -x, using p=1 mod4.
w=bytearray(p)
for y in range(1,(p+1)//2):w[y*y%p]=1
def count(r):
    j=(3-r)**2%p
    def fiber(x):
        f=x*(x*x-j)%p
        return 1 if f==0 else 2*w[f]
    return 2+2*sum(fiber(x)for x in range(1,(p+1)//2))
arms=K['arms']
rs=[r['root']for r in arms]
assert rs==[8296152,1511497] and all(r*r%p==2 for r in rs)
counts=[count(r) for r in rs]; orders=[r['order']for r in arms]
assert counts==[9813764,9801536] and gcd(*counts)==4
assert orders==[2453441,29]
h,L=map(int,(D['simultaneous_h_residue'],D['simultaneous_h_modulus']))
assert L%orders[0]==L%orders[1]==0 and h%orders[0]==0 and h%orders[1]==1
assert L%p**4==0 and h%p**4==p**3
print(json.dumps({'prime':p,'slot':292,'root_theta':[1,2399],
                  'roots_of_two':rs,'group_counts':counts,'group_gcd':gcd(*counts),
                  'orders':orders,'retained_T_mod_p2':K['T_j_mod_p2'][2]},indent=2))
