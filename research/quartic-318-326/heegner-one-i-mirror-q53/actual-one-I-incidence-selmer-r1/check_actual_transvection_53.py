#!/usr/bin/env python3
"""Actual degree-13 residue readout for the ℓ=53 transvection sieve."""
import hashlib,json
from pathlib import Path
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
H=Path(__file__).resolve().parent
p=H.parent/'actual-one-I-cyclotomic13-r1'/'EXACT-POINT-FIELD-13.json'
raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a'
j=json.loads(raw);d=j['d'];q=53;n=q**13
x=s.symbols('u')
F=s.Poly.from_list(j['x_root_poly_coefficients'],x,modulus=q)
assert F.gcd(F.diff()).degree()==0
picks=sorted(tuple(int(a)%q for a in f.monic().all_coeffs()) for f,e in F.factor_list()[1] if f.degree()==13)
assert len(picks)==6
h=list(picks[0]);zero=[];one=[1];u=[1,0]
def c(a):return [a%q] if a%q else []
def add(a,b):return g.gf_add(a,b,q,ZZ)
def sub(a,b):return g.gf_sub(a,b,q,ZZ)
def mul(a,b):return g.gf_rem(g.gf_mul(a,b,q,ZZ),h,q,ZZ)
def pw(a,z):return g.gf_pow_mod(a,z,h,q,ZZ)
def inv(a):
    assert a
    b=pw(a,n-2)
    assert mul(a,b)==one
    return b
def div(a,b):return mul(a,inv(b))
assert pw(u,n)==u
assert g.gf_gcd(sub(pw(u,q),u),h,q,ZZ)==one # 13 is prime
G=mul(u,mul(sub(u,c(1)),add(u,c(3))))
R=mul(c(pow(13,4,q)*d),G)
def sqrt(a):
    assert a and pw(a,(n-1)//2)==one and (n-1)%8==4
    z=next(c(v) for v in range(2,q) if pw(c(v),(n-1)//2)==c(-1))
    S=(n-1)//4
    r=pw(a,(S+1)//2)
    if mul(r,r)!=a:r=mul(r,pw(z,S))
    assert mul(r,r)==a
    return r
W=sqrt(R)
# Deterministic choice of sign for the residue address.
W=min(W,sub(zero,W))
P=(mul(c(d),u),mul(c(d*pow(169,-1,q)),W))
a2=c(2*d);a4=c(-3*d*d)
def plus(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;v,w=Q
    if x==v and add(y,w)==zero:return None
    if x==v:m=div(add(add(mul(c(3),mul(x,x)),mul(c(2),mul(a2,x))),a4),mul(c(2),y))
    else:m=div(sub(w,y),sub(v,x))
    X=sub(sub(sub(mul(m,m),a2),x),v)
    return X,sub(mul(m,sub(x,X)),y)
V={}
T=None
for a in range(1,13):
    T=plus(T,P);assert T is not None
    xx,yy=T
    assert mul(yy,yy)==mul(xx,add(add(mul(xx,xx),mul(a2,xx)),a4))
    V[a]=(mul(c(13*pow(d,-1,q)),xx),mul(c(169*pow(d,-1,q)),yy))
assert plus(T,P) is None and pw(u,q)!=u
zeta=16
assert pow(zeta,13,q)==1 and zeta!=1
def score(xs,proj=True):
    t=one
    for a,x in xs.items():
        assert x
        k=(pow(12,-1,13)*pow(a,-1,13))%13 if proj else 1
        t=mul(t,pw(x,k))
    w=pw(t,(n-1)//13)
    return next(i for i in range(13) if w==c(pow(zeta,i,q)))
score_even=score({i:v for i,(v,w) in V.items()})
mixed={}
for a in range(1,q):
    vals={i:add(c(a),w) for i,(v,w) in V.items()}
    if all(vals.values()):
        mixed[str(a)]=score(vals)
        if mixed[str(a)]:break
score_mixed=next((j for j in mixed.values() if j),0)
assert score_even==0 and score_mixed!=0
# E_d(F53) has 13-primary order exactly13, so the repeated
# eigenvalue 1 is nonscalar, independently of the field construction.
table=[0]*q
for y in range(q):table[y*y%q]+=1
card=1+sum(table[(x*(x-d)*(x+3*d))%q] for x in range(q))
assert card==52 and (q+1-card)%13==2
print(json.dumps(dict(d=d,ell=q,exact_count=card,irreducible_degree13_factor_desc=h,
  chosen_W_in_u_basis_desc=W,point_branch_nonfixed=True,
  e_lambda_even_v_score=score_even,e_lambda_mixed_c_plus_W_scores=mixed,zeta13_mod53=zeta),
  sort_keys=True,indent=2))
