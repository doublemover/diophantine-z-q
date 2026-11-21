#!/usr/bin/env python3
"""One old prime and six degree-2 mirror primes with the same local row."""
from pathlib import Path
import hashlib,json,contextlib,io,runpy
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
H=Path(__file__).resolve().parent.parent
def get(path,pin):
    a=(H/path).read_bytes()
    assert hashlib.sha256(a).hexdigest()==pin
    return H/path
fn=get("actual-one-I-q53-global-norm-r1/check_q53_small_support.py",
 "57703b33ad73461f5b9124520d77baea79592f6ce52c92bef68d933171487b36")
with contextlib.redirect_stdout(io.StringIO()) as out:
    m=runpy.run_path(str(fn))
assert hashlib.sha256(out.getvalue().encode()).hexdigest()=="b85b7501298bfcbf59a28e650bd5fe015f946d32b9f2178ba68418bb64557de3"
j=json.loads(out.getvalue());r=j["p5303"]
E=get("actual-one-I-mirror-even-tower-r1/EXACT-MIRROR-EVEN-TOWER-AND-CHARTS.json",
 "962cc16a0b4a09cb9469dfd286bec9976b51aeca6ac7ecf6c77a255aafc505d0")
J=json.loads(E.read_text());d=j["d"];assert d==J["d"]
ell=r["test_rational_prime"];assert ell==5303
nr=m["nr"]; R=m["Ring"](ell,1,[1,0,-nr]);c,A,S,M,pw=R.c,R.add,R.sub,R.mul,R.pw
z0=next(w for a in range(1,ell) if (w:=pw([1,a],(ell**2-1)//13))!=[1])
z=z0
scale=J["relative_normalization_divides_Z_squared_by"]
D=R.c(scale);assert D
Ymin=J["absolute_even_degree84_polynomial_desc"]
f0=[a%ell for a in Ymin];assert g.gf_gcd(f0,g.gf_diff(f0,ell,ZZ),ell,ZZ)==[1]
group=lambda u,v:m["group"](R,u,v)
P=(c(d*r["u_in_unramified_quad"]),M(r["W"],c(d*pow(169,-1,ell))))
RHS=lambda x:x*(x-d)*(x+3*d)%ell
roots={}
for u in range(ell):
    roots.setdefault(u*u%ell,u)
N=1+sum(1 if not a else 2*(a in roots) for a in map(RHS,range(ell)))
assert N==5200==13*400
def times(n,P):
    T=None
    while n:
        if n&1:T=group(T,P)
        n//=2
        if n:P=group(P,P)
    return T
Q=next(Q for x in range(ell) if RHS(x) in roots and
       (Q:=times(400,(c(x),c(roots[RHS(x)])))) is not None)
assert times(13,Q) is None and times(13,P) is None
def frob(P):return tuple(pw(a,ell) for a in P)
assert frob(Q)==Q and frob(P)==(P[0],S([],P[1]))
def mark(p):
    B=[]; Z=[]
    for a in range(1,13):
        x,y=times(a,p)
        if a<=6:B=A(B,M(x,c(pow(2*d,-1,ell))))
        Z=A(Z,M(pw(z,a),M(y,c(169*pow(d,-1,ell)))))
    Y=R.div(M(Z,Z),D)
    assert not R.ev(Ymin,Y)
    return B,Y,Z
# Bind the orientation by the archived actual (B,Z), not by its
# chosen_zeta_power metadata: the old program reuses that loop variable
# during its 3-adic pass before serializing. The selected ideal is correct.
phase=[]
for a in range(1,13):
    z=pw(z0,a)
    b0,y0,zz0=mark(P)
    if (b0,zz0)==([r["B"]],[r["Z"]]):phase.append(a)
a,=phase
z=pw(z0,a)
assert pw(z,13)==[1] and pw(z,ell)==R.inv(z)
def pad(a):return ([0]*(2-len(a))+a)
stars=[]
for i in range(1,7):
    T=group(P,times(i,Q));b0,y,zz=mark(T)
    Tneg=group(P,times(13-i,Q));bb,yy,zn=mark(Tneg)
    assert (bb,yy,zn)==(pw(b0,ell),pw(y,ell),pw(zz,ell))
    assert len(y)==2 and len(zz)<=2 and len(b0)==2 and zz
    y1,y0=pad(y); z1,z0=pad(zz)
    la=z1*pow(y1,-1,ell)%ell; mu=(z0-la*y0)%ell
    assert A(M(c(la),y),c(mu))==zz
    Y2=pw(y,ell); h=[1,(-A(y,Y2)[0])%ell,M(y,Y2)[0]]
    assert g.gf_irreducible_p(h,ell,ZZ)
    assert g.gf_rem(f0,h,ell,ZZ)==[]
    assert not R.ev(h,y)
    stars.append(dict(index=i,old_B_desc=b0,even_Y_minpoly_desc=h,Z_as_linear_Y_desc=[la,mu],
                   exact_mod13_target_multiple_of_q5303=2))
assert len({tuple(r["even_Y_minpoly_desc"]) for r in stars})==6
print(json.dumps(dict(d=d,prime=ell,old_mirror_prime=r,
    rational_fixed_point_Q=[Q[0],Q[1]],norm_of_new_ideal=ell**2,
    actual_zeta_phase_recovered_by_old_B_and_Z=a,
    new_even_field_charts=stars,no_actual_class_independence_claim=True),
    sort_keys=True,indent=2))
