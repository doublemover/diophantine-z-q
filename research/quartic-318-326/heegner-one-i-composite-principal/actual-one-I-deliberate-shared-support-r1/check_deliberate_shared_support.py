#!/usr/bin/env python3
"""Prove exact cancellation at every prime over C, not just one residue."""
from pathlib import Path
from math import gcd
import contextlib, hashlib, io, json, runpy
H=Path(__file__).resolve().parent
P=H.parent/'actual-one-I-principal-composite-r1'
parent_script=P/'check_composite_principal_support.py'
assert hashlib.sha256(parent_script.read_bytes()).hexdigest()=='39046ae66f92a455d41fb50d1a3d0fe470f988d67a5380327845b48a57516d19'
with contextlib.redirect_stdout(io.StringIO()) as out:
    x=runpy.run_path(str(parent_script))
data=json.loads(out.getvalue())
assert hashlib.sha256(out.getvalue().encode()).hexdigest()=='7eca9c5a866bde202054ea426b699d45ebc1de671a27b500b611bc1deb19e238'
N=data['unfactored_cofactor_ideals'][0]['N'];z=data['small5881']
p=z['N'];u0=z['u'];D=3*p
f=x['f'];G=x['G'];n=x['B_num'];b=x['B_den'];d=x['d'];mgcd=x['mgcd'];ev=x['ev']
# D+W+169B is the numerator of r=1+(W+169B)/D.
# Need no root at *any* of the geometric 13-point labels mod p | N.
gcd_den=mgcd(f.all_coeffs(),b.all_coeffs(),N)
assert gcd_den==[1]
shift_norm=(D*b+169*n)**2-169**2*d*G*b**2
gcd_all=mgcd(f.all_coeffs(),shift_norm.all_coeffs(),N)
assert gcd_all==[1]
# At the *opposite* degree-one prime over5881, W+169B vanishes
# and must be divided by p before testing whether r is a unit.
m=p*p
up=(u0-ev(f.all_coeffs(),u0,m)*pow(ev(f.diff().all_coeffs(),u0,p),-1,p))%m
assert up%p==u0 and ev(f.all_coeffs(),up,m)==0
B=ev(n.all_coeffs(),up,m)*pow(ev(b.all_coeffs(),up,m),-1,m)%m
v=13*up%m; R=13*d*v*(v-13)*(v+39)%m
W0=-z['W']%p
Wp=(W0-(W0*W0-R)*pow(2*W0,-1,p))%m
assert Wp%p==W0 and (Wp*Wp-R)%m==0
alt=(Wp+169*B)%m
assert alt%p==0 and alt//p!=0
r_opposite=(1+(alt//p)*pow(3,-1,p))%p
assert r_opposite!=0
# At q3 the valuation of its 3*5881 denominator is 13,
# while W+169B is the negative of the old alpha at the opposite label.
vals0={int(k):v for k,v in x['dct']['nonformal_3_valuations_by_scalars'].items()}
vals_r={k:vals0[13-k]-13 for k in range(1,13)}
weight=lambda R:sum(v*pow(k,-1,13) for k,v in R.items())*pow(12,-1,13)%13
assert weight(vals0)==11 and weight(vals_r)==2
print(json.dumps(dict(actual_d=d,denominator=D,
    exact_cofactor_2379_digit_C_sha256=hashlib.sha256(str(N).encode()).hexdigest(),
    relative_shift_norm_degree=shift_norm.degree(),
    denom_and_shift_norm_monic_gcds_mod_C=[gcd_den,gcd_all],
    r_nonformal_3_valuations_by_scalars=vals_r,
    e_lambda_r_at_q3_normalized_coefficient=weight(vals_r),
    r_5881_opposite_root_u_mod_p2=up,r_5881_opposite_root_W_mod_p2=Wp,
    r_5881_opposite_B_mod_p2=B,r_5881_opposite_cancellation_witness=alt//p,
    r_5881_opposite_residue_unit=r_opposite,
    r_coeff_in_e_lambda_basis_at_labelled_q3=-2,
    r_coeff_in_e_lambda_basis_at_labelled_q5881=-1),
    sort_keys=True,indent=2))
