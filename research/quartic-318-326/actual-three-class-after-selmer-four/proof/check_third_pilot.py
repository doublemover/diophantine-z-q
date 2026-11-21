#!/usr/bin/env python3
"""One true lifted detector row; independent of any uncomputed new prime."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd, prod
from pathlib import Path
import json, runpy
base=Path(__file__).resolve().parent.parent
def pin(name,h):
    f=base/name
    assert sha256(f.read_bytes()).hexdigest()==h
    return f
j=json.loads(pin('linked-detector-gaussian-order29-new-classes-r1/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json',
      '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1').read_bytes())
with redirect_stdout(StringIO()):
    d=runpy.run_path(str(pin('linked-detector-two-class-fixed-selmer-quotient-r1/check_fixed_quotient_known_rows.py',
      '082b8c90ee5afc55c27d0bc042457eaff9f4c5f37294bce387e7eee4aab92150')))
d['labels'].__globals__['s']=1+d['i']
assert str(d['J'])==j['literal_scalar_J']
p,r,N,M=6469193,33934,202249,29
ch=lambda u:1 if pow(u%p,(p-1)//2,p)==1 else -1
assert d['prime'](p) and p%8==1 and ch(7)==-1 and 1387**2+2132**2==p
L=int(j['simultaneous_h_modulus']); h=int(j['simultaneous_h_residue'])
assert gcd(L,N)==17 and h%17==0 and L%29==0 and h%29==1 and L%p==315286
assert gcd(L*N*M*p,2399)==1
h1,L1=d['crt'](h,L,0,N)
h2,L2=d['crt'](h1,L1,1,M)
h3,L3=d['crt'](h2,L2,p**3,p**4)
assert h3%2==0 and L3%2==0 and h3%L==h%L
G=[(1387-1)**2+2132**2,(1387+1)**2+2132**2]
assert gcd(*G)==4 and sum(k%N==0 for k in G)==sum(k%M==0 for k in G)==1
pp=p*p
arms=[]
for ro,o in [(r,N),(p-r,M)]:
    lift=ro+p*(((2-ro*ro)//p)*pow(2*ro,-1,p)%p)
    assert lift*lift%pp==2
    _,P,U,isformal=d['F'](p,lift)
    fac=tuple(d['prime_factors'](o))
    assert isformal(P(o)) and all(not isformal(P(o//q)) for q in fac)
    assert P(o)!=(0,0)
    ns=d['labels'](p*o,(*fac,p))
    us=[U(P(n))[0] for n in ns]
    z=prod(-pow(u,-1,pp) for u in us)%pp
    arms.append({'root':ro,'root_mod_p2':lift,'point_order':o,'labels_mod_period':ns,
                 'U_charts':us,'shallow_product':z})
x,y=[a['shallow_product'] for a in arms]
scales=[1,((x+y)*pow(2,-1,pp)+x*y)%pp,x*y%pp]
assert all(c%p for c in scales)
theta=[0,-pow(2,-1,pp)%pp,pp-1,pow(2399,-1,pp),-32*pow(407,-1,pp)%pp]
scaled_roots=[[q*pow(c*c,-1,p)%p for q in theta[1:]]for c in scales]
assert len({v for z in scaled_roots for v in z})==12
assert all(v for z in scaled_roots for v in z)
z0=1064003; target=(theta[3]+p)%pp
assert z0*z0%p==target%p
w=(z0+p*(((target-z0*z0)//p)*pow(2*z0,-1,p)%p))%pp
Ts=[(c*w)**2%pp for c in scales]
values=[prod(x-q for q in theta)%pp for x in Ts]
assert all(T%p!=1 for T in Ts) and Ts[0]==target
assert values[0]%p==0 and values[0]!=0 and all(x%p for x in values[1:])
s,t,u=scaled_roots[1][3],scaled_roots[2][2],scaled_roots[0][2]
assert u==w*w%p
print(json.dumps({'p_c':p,'slot':190,'unordered_groups':G,'arms':arms,
                  'scales_mod_p2':scales,'scaled_roots_mod_p':scaled_roots,
                  'target_W_mod_p2':w,'T_j_mod_p2':Ts,'F_j_mod_p2':values,
                  'unit_quotient_a_b_bits':[ch(u-s),ch(u-t)],
                  'L_mod_p': L%p,'gcd_L_primary':gcd(L,N),'h_mod_29':h%29,
                  'new_h_residue':str(h3),'new_h_modulus':str(L3),
                  'new_h_modulus_mod_2399':L3%2399},indent=2))
