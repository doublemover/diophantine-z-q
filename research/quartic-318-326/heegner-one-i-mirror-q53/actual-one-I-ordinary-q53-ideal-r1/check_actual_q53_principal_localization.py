#!/usr/bin/env python3
"""Explicit q53 generators and one principal element of exact local depth one."""
from pathlib import Path
import contextlib,hashlib,io,json,runpy
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
H=Path(__file__).resolve().parent
def pull(rel,script,output):
    p=H.parent/rel
    assert hashlib.sha256(p.read_bytes()).hexdigest()==script
    with contextlib.redirect_stdout(io.StringIO()) as out:
        m=runpy.run_path(str(p))
    assert hashlib.sha256(out.getvalue().encode()).hexdigest()==output
    return m,json.loads(out.getvalue())
md,arch=pull('actual-one-I-mirror-ray-class-r1/check_actual_mirror_53.py',
 '27ce42ba852dca432507c4a40bc53d9759b6d23411518bebccd05c95f6212b0d',
 'a0870144f7cdb7d84a1e0f4a1c9e19cd7afc69ca2f5ff81a295341eeff35dc7d')
_,deg1=pull('actual-one-I-incidence-selmer-r1/check_point_covector_incidence.py',
 'e884e8615fb047d22e8e36a3837e032b9d807d1bc699bd0da7fa0f0bba107177',
 '7986d3b3199d5e7780ed001297c0a78e0eb7a8b8ae93e624d95b4a6a0a664d64')
q=53; h=arch['source_u_factor_desc']; d=arch['d']; half=q//2
m=md['m']; Pz=md['Z']; PB=md['B']; minb=md['b']; co=md['co']
c, add, mul, pw, ev = m['c'],m['add'],m['mul'],m['pw'],None
def eval_ring(f,a,add,mul,c):
    r=[]
    for u in f:r=add(mul(r,a),c(u))
    return r
# The relative nonfixed branch of the degree14 line field is the
# degree13 minpoly of B; its other root is the fixed-line value.
_,lin=g.gf_div([a%q for a in co],minb,q,ZZ)
assert lin==[]
line=g.gf_quo([a%q for a in co],minb,q,ZZ)
assert len(line)==2 and line[0]==1
bf=(-line[1])%q
m_at_f=g.gf_eval(minb,bf,q,ZZ)
assert m_at_f
powers=[pw(PB,i) for i in range(13)]
def padded(a):return ([0]*(13-len(a))+a)[::-1]
V=[list(r)+[t] for r,t in zip(zip(*[padded(a) for a in powers]),padded(Pz))]
for k in range(13):
    s=next(i for i in range(k,13) if V[i][k]);V[k],V[s]=V[s],V[k]
    inv=pow(V[k][k],-1,q);V[k]=[a*inv%q for a in V[k]]
    for i in range(13):
        if i!=k:
            a=V[i][k];V[i]=[(b-a*c)%q for b,c in zip(V[i],V[k])]
assert all(r[:13]==[int(i==j) for j in range(13)] for i,r in enumerate(V))
G=[(r[-1]+half)%q-half for r in V][::-1]
assert eval_ring(G,PB,add,mul,c)==Pz
nonfixed=[]
for b in range(1,13):
    z=[]
    for a,(_,w) in m['V'].items():z=add(z,mul(c(pow(16,a*b,q)),w))
    nonfixed.append(z)
assert len(set(map(tuple,nonfixed)))==12 and nonfixed[0]==Pz
# Shift by t*m_B(B) to avoid every degree-one mirror residue as well.
for t in range(q):
    off=(-int(g.gf_eval(G,bf,q,ZZ))+t*m_at_f)%q
    if all((z+off)%q for z in deg1['gauss_resolvent_conjugates_mod53']):break
else:raise AssertionError
D=q*q
def C(a):
    return [a%D] if a%D else []
def A(a,b):return g.gf_add(a,b,D,ZZ)
def S(a,b):return g.gf_sub(a,b,D,ZZ)
def M(a,b):return g.gf_rem(g.gf_mul(a,b,D,ZZ),h,D,ZZ)
def reduce(a):return g.gf_strip([x%q for x in a])
def I(a):
    u=m['inv'](reduce(a))
    r=M(u,S(C(2),M(a,u)))
    assert M(a,r)==[1]
    return r
def div(a,b):return M(a,I(b))
def Ev(f,a):return eval_ring(f,a,A,M,C)
def diff(P):return [(len(P)-1-i)*a for i,a in enumerate(P[:-1])]
f=m['j']['x_root_poly_coefficients']
u=[1,0]
up=S(u,M(Ev(f,u),I(Ev(diff(f),u))))
assert not Ev(f,up) and reduce(up)==u
v=M(C(13),up)
R=M(C(13*d),M(v,M(S(v,C(13)),A(v,C(39)))))
W0=m['W']
W=S(W0,div(S(M(W0,W0),R),M(C(2),W0)))
assert M(W,W)==R and reduce(W)==W0
Z0=16
zeta=(Z0-(pow(Z0,13,D)-1)*pow(13*pow(Z0,12,q)%q,-1,q))%D
assert pow(zeta,13,D)==1 and zeta%q==16
P=(M(C(d),up),M(C(d*pow(169,-1,D)),W))
def plus(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u and not A(y,v):return None
    if x==u:z=div(A(A(M(C(3),M(x,x)),M(C(4*d),x)),C(-3*d*d)),M(C(2),y))
    else:z=div(S(v,y),S(u,x))
    a=S(S(S(M(z,z),C(2*d)),x),u)
    return a,S(M(z,S(x,a)),y)
B2=[]; Z2=[];T=None
for a in range(1,13):
    T=plus(T,P);assert T is not None
    x,y=T
    if a<=6:B2=A(B2,M(C(pow(2*d,-1,D)),x))
    Z2=A(Z2,M(C(pow(zeta,a,D)*169*pow(d,-1,D)),y))
assert plus(T,P) is None and reduce(B2)==PB and reduce(Z2)==Pz
val=A(S(Z2,Ev(G,B2)),M(C(t),Ev(minb,B2)))
assert reduce(val)==[]
shift=0
if not val:shift=q;val=A(val,C(q))
assert reduce(val)==[] and val
gamma_div_53=[v//q for v in val]
assert any(gamma_div_53)
print(json.dumps(dict(d=d,ell=q,norm=q**13,m_B_degree13_desc=minb,
   Z_equals_G_of_B_desc=G,remaining_degree1_B=bf,
   distinct_degree13_Z_values=len(set(map(tuple,nonfixed))),
   numerator_shift_m_B_coefficient=t,numerator_extra_scalar=shift,
   exact_gamma_div53_residue_desc=gamma_div_53,
   numerator_description='Z - G(B) + t*m_B(B) + scalar',
   only_q53_above_rational_53=True,normalized_q53_exponent=1),
 sort_keys=True,indent=2))
