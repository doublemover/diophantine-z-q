#!/usr/bin/env python3
"""Complete support and fixed Jacobi signs; genuine nineteen W cells."""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from flint import fmpz
from math import prod
import json
root=Path(__file__).resolve().parents[1]
q=root/'linked-detector-numeric-anchor-phase-repair-r1/EXACT-PRIMARY-REPAIRED-COVER.json'
a=json.loads(q.read_bytes())
u,b,t=258049,10568037907556089,F(1,2399)
assert a['b']==b
cells=[(p,w) for p,w,_,_ in a['old_cells_W_a_unit_b_unit']]+[
 (r['p'],r['W_mod_p2']) for r in a['actual_new_contacts']]
assert len(cells)==len({p for p,_ in cells})==19
lam=F(16*u**4+24*u*u+1,32*u*u)
n=lam+t
def chi(z,p):
    k=pow(z%p,(p-1)//2,p)
    return {0:0,1:1,p-1:-1}[k]
FU=[11,23459]
FL=[97,36833,966041,20555323601]
FD=[3,51071,226691,4900372089410977]
assert all(fmpz(p).is_prime() for p in [*FU,*FL,*FD])
assert prod(FU)==u and prod(FL)==lam.numerator and prod(FD)==n.numerator
assert all(chi(b,p)==1 or chi(2,p)==1 for p in FU)
assert all(chi(b,p)==1 for p in FD)
phase=[]
for p,w in cells:
    v=(16*u**4+(24+32*w*w)*u*u+1)%p
    assert chi(v,p)==1 and p%8==1
    phase.append([p,w,v])
W0,Y0=F(4619710060,2399*38613147),F(41,2399*38613147)
assert W0*W0-b*Y0*Y0==t
assert 38613147==3*12871049 and fmpz(12871049).is_prime() and chi(2,12871049)==1
assert chi(b,3)==1 and W0.denominator%3==Y0.denominator%3==0
assert (W0.denominator//3)%3 and (Y0.denominator//3)%3
assert W0.numerator%3 and Y0.numerator%3
m=lambda D,k:D.numerator*pow(D.denominator,-1,k)%k
assert (m(W0,8),m(Y0,8),b%32)==(4,5,25)
assert [r for r in range(8) if any((r+8*i)**2%32==25 for i in range(4))]==[3,5]
assert [m(W0,8)-r*m(Y0,8) for r in (3,5)]==[-11,-21]
assert [x%8 for x in (-11,-21)]==[5,3]
assert b%8==1 and m(b*t,16)==7 and b%3==1
print(json.dumps(dict(u=u,b=b,Lambda=[lam.numerator,lam.denominator],
    Lambda_plus_t=[n.numerator,n.denominator],u_support=FU,Lambda_numerator=FL,
    difference_numerator=FD,seed_residues_W0_Y0_mod8=[4,5],stable_pairing_bits={'2':1,'3':1},
    all_nineteen_local_rows=phase),indent=2))
