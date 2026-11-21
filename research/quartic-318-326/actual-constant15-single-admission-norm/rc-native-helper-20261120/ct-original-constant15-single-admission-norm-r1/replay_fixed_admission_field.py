from math import isqrt, prod
from pathlib import Path
import json
root=Path(__file__).resolve().parent.parent
old=json.loads((root/'ct-original-scalar-mestre-marked-selmer-r1'/'EXACT-MARKED-SELMER-ROWS.json').read_text())
P=tuple(old['visible'])
B=tuple(P[:8]); V=tuple(P[8:]); E=(5,11,17,1489,131,6551,2470991)
e=prod(E); T=prod(V); L=7129
assert e==2952271997968816765 and T==35589230039008870789
assert L>1 and all(L%q for q in range(2,isqrt(L)+1))
def leg(z,p):
    h=pow(z%p,(p-1)//2,p)
    assert h in (1,p-1)
    return 1 if h==1 else -1
stripped=tuple((-1)**x for x in old['true_d_stripped_bits'])
known_psi=[]; hidden_ramified_bits={}
for p,d_p in zip(P,stripped):
    a=int(p in E)
    unit_e=e//(p**a)
    required=1 if not a else leg(-1,p)*d_p
    assert leg(unit_e,p)==required
    known_psi.append([p,a,required])
    if a:
        u_p=d_p*leg(prod(q for q in P if q!=p),p)
        assert leg(L,p)==u_p
        hidden_ramified_bits[p]=u_p
assert [p for p,x in hidden_ramified_bits.items() if x==-1]==[17,2470991]
assert all(leg(5,p)==1 for p in V) and T%5==4
assert L%24==1 and leg(5,L)==leg(e,L)==1
assert e%3==1 and e%8==5 and (e//5)%5==3
def polynomial(x,y,z,w):
    return (x*x+5*y*y-e*z*z-5*e*w*w)**2-20*(x*y-e*z*w)**2
assert polynomial(0,1,0,0)==25 and polynomial(0,0,1,0)==e*e
assert polynomial(0,0,0,1)==25*e*e
print(json.dumps(dict(e=e,T=T,L=L,coprime_auxiliary_split=[1,1],known_psi_places=known_psi,
    hidden_stripped_signs_on_e=hidden_ramified_bits,full_degree_place=5,e_over_five_mod_five=(e//5)%5,
    norm_samples=[polynomial(1,2,3,4),polynomial(2,-4,-6,9)]),indent=2))
