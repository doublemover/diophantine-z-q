#!/usr/bin/env python3
"""Exact degree-13 ray test-prime residue address in the actual mirror field."""
from pathlib import Path
import contextlib,hashlib,io,json,runpy
H=Path(__file__).resolve().parent
p=H.parent/'actual-one-I-incidence-selmer-r1'/'check_actual_transvection_53.py'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='ac5fc98a08653e55f4276ad959ccd46365445eb15d8e33e7d320606467a65d2a'
with contextlib.redirect_stdout(io.StringIO()) as h:
    m=runpy.run_path(str(p))
assert hashlib.sha256(h.getvalue().encode()).hexdigest()=='ded42d7df018fd526c3a57a61d8d33a92395733a32e086e15aefc4cd989230c6'
q=m['q']; V=m['V']; d=m['d'];c=m['c'];add=m['add'];mul=m['mul'];pw=m['pw']
sub=m['sub'];h=m['h'];zeta=m['zeta'];one=m['one'];zero=m['zero']
B=[];Z=[]
for a,(v,W) in V.items():
    if a<=6:B=add(B,mul(c(pow(26,-1,q)),v))
    Z=add(Z,mul(c(pow(zeta,a,q)),W))
assert pw(B,q)!=B and pw(Z,q)!=Z and pw(Z,q**13)==Z and pw(B,q**13)==B
def minpoly(z):
    M=[one]
    a=z
    for _ in range(13):
        M=[sub(x,mul(a,y)) for x,y in zip(M+[zero],[zero]+M)]
        a=pw(a,q)
    assert all(len(a)<=1 for a in M)
    return [int(x[0]) if x else 0 for x in M]
b=minpoly(B);z=minpoly(Z)
# Literal coordinate B must agree with the previously computed line polynomial.
p=H.parent/'actual-one-I-explicit-line-field-r2'/'ACTUAL-FIELD-DISCRIMINANTS.json'
raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='b9573239c447acd8f6e3d52d412e3041f9a2a19dd50496b2c58ee45afac68e84'
co=json.loads(raw)['integral_scaled_line_polynomial_desc']
F=[]; ZZ=[]
for a in co:F=add(mul(F,B),c(a))
for a in z:ZZ=add(mul(ZZ,Z),c(a))
assert F==ZZ==zero
p13=13;e=156
whole_cut=e+e//(p13-1)+1
power_leads={min(p13*j,e+j) for j in range(1,whole_cut)}
grades=[j for j in range(1,whole_cut) if j%12==1 and j not in power_leads]
assert whole_cut==170 and grades==[1]+list(range(25,158,12)) and len(grades)==13
assert max(grades)+1==158
print(json.dumps(dict(d=d,ell=q,actual_residue_degree=13,norm_of_mirror_test_prime=q**13,
    mirror_ramified_13_local_faithful_unit_grades=grades,mirror_faithful_ray_modulus_exponent=158,
    source_u_factor_desc=h,cyclotomic_root_mod53=zeta,
    line_B_in_u_basis_desc=B,mirror_Z_in_u_basis_desc=Z,
    line_B_minpoly_desc=b,mirror_Z_minpoly_desc=z),sort_keys=True,indent=2))
