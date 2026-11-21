from pathlib import Path
from math import prod,isqrt
import json
src=Path(__file__).resolve().parent.parent
row=json.loads((src/'ct-original-scalar-mestre-marked-selmer-r1/EXACT-MARKED-SELMER-ROWS.json').read_text())
ret=json.loads((src/'ct-original-constant15-nonnorm-retune-107-r1/EXACT-107-RETUNE-CONTROLS.json').read_text())
P=tuple(row['visible'])+(107,)
D=tuple(row['true_d_stripped_bits'])+(0,)
assert ret['delta_mod_p2']==107
a=590454399593763353
f=ret['known_opposite_class_e2']; assert f==65029284442765
A=(11,17,1489,131,6551,2470991)
B=(5,17,107,733,1489,6551)
assert a==prod(A) and f==prod(B)
T=prod(P[8:]); L=937
assert L%24==1 and all(L%p for p in range(2,isqrt(L)+1))
def ell(x,p):
    w=pow(x%p,(p-1)//2,p)
    assert w in (1,p-1)
    return int(w==p-1)
C={p:D[j]^ell(prod(q for q in P if q!=p),p) for j,p in enumerate(P)}
fixed=[]
for p,dp in zip(P,D):
    ram=p in B
    f_unit=f//p if ram else f
    assert ell(f_unit,p)==(dp^ell(-1,p) if ram else 0)
    fixed.append([p,int(ram),ell(f_unit,p)])
for p in A+B:
    assert ell(L,p)==C[p]
assert sorted({p for p in A+B if C[p]})==[5,11,1489]
assert ell(a,L)==ell(f,L)==0 and a%5==3 and f%5==0 and f%25!=0
assert a%8==1 and f%8==5 and f%3==1
assert ell(a,107)==0
print(json.dumps(dict(a=a,f=f,T_with_107=T,repair_prime=L,full_local_degree_at=5,
    fixed_opposite_unit_tests=fixed,required_nonsquare_corrections=[5,11,1489]),indent=2))
