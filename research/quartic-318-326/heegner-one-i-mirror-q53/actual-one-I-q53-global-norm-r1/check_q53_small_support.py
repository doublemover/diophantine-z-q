#!/usr/bin/env python3
"""Resolve the actual visible 3/5303 principal factors in the mirror quotient."""
from pathlib import Path
import hashlib,json
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
H=Path(__file__).resolve().parent
def read(rel,sha):
    raw=(H/rel).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==sha
    return json.loads(raw)
j=read('../actual-one-I-ordinary-q53-ideal-r1/EXACT-ORDINARY-Q53-IDEAL-AND-PRINCIPAL-CHART.json',
       'f5e25122b2b58fe2d14ab66aa1bc61992a6446df8d3b4603e460129030da3dc2')
n=read('ACTUAL-Q53-GLOBAL-PRINCIPAL-NORM.json',
       '31adfcc272aaf806a8cb3838ff58b7d33f5ab3fc1e94dbfd9ad043b79d445079')
k=read('../actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json',
       '7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a')
assert j['d']==n['d']==k['d']
d=j['d']; G=j['Z_equals_G_of_B_desc']; F=k['x_root_poly_coefficients']
class Ring:
    def __init__(self,p,e,h):
        self.p=p;self.e=e;self.q=p**e;self.h=h;self.f=len(h)-1
    def c(self,a):
        return [a%self.q] if a%self.q else []
    def add(self,a,b):return g.gf_add(a,b,self.q,ZZ)
    def sub(self,a,b):return g.gf_sub(a,b,self.q,ZZ)
    def mul(self,a,b):return g.gf_rem(g.gf_mul(a,b,self.q,ZZ),self.h,self.q,ZZ)
    def pw(self,a,b):return g.gf_pow_mod(a,b,self.h,self.q,ZZ)
    def inv(self,a):
        x=g.gf_strip([b%self.p for b in a]);assert x
        r=g.gf_pow_mod(x,self.p**self.f-2,self.h,self.p,ZZ)
        for _ in range(self.e):
            r=self.mul(r,self.sub([2],self.mul(a,r)))
        assert self.mul(a,r)==[1]
        return r
    def div(self,a,b):return self.mul(a,self.inv(b))
    def ev(self,c,x):
        z=[]
        for a in c:z=self.add(self.mul(z,x),self.c(a))
        return z
    def val(self,a):
        for i in range(self.e):
            if any(t%(self.p**(i+1)) for t in a):return i
        return self.e
def group(R,P,Q):
    if P is None:return Q
    if Q is None:return P
    a,b=P;x,y=Q; c=R.c;A=R.add;S=R.sub;M=R.mul
    if a==x and not A(b,y):return None
    if a==x:m=R.div(A(A(M(c(3),M(a,a)),M(c(4*d),a)),c(-3*d*d)),M(c(2),b))
    else:m=R.div(S(y,b),S(x,a))
    X=S(S(S(M(m,m),c(2*d)),a),x)
    return X,S(M(m,S(a,X)),b)
def read_Z(R,z,W):
    return [
      sum_ring(R,[R.mul(w,R.pw(z,a*j)) for a,w in enumerate(W,1)])
      for j in range(1,13)]
def sum_ring(R,values):
    a=[]
    for x in values:a=R.add(a,x)
    return a
# Actual mirror 5303 degree-one prime; the point itself is eigenvalue -1.
ell=5303
assert s.isprime(ell) and ell%13==12 and n['exact_small_rational_norm_factors'][str(ell)]==1
nr=next(a for a in range(2,ell) if pow(a,(ell-1)//2,ell)==ell-1)
R=Ring(ell,1,[1,0,-nr])
z=next(w for a in range(1,ell) if (w:=R.pw([1,a],(ell**2-1)//13))!=[1])
assert R.pw(z,13)==[1] and R.pw(z,ell)==R.inv(z)
u=s.symbols('u')
Fq=s.Poly.from_list(F,u,modulus=ell)
assert Fq.gcd(Fq.diff()).degree()==0
roots=sorted(-int(f.monic().TC())%ell for f,e in Fq.factor_list()[1] if f.degree()==1)
matches={}
for u0 in roots:
    Wsq=13**4*d*u0*(u0-1)*(u0+3)%ell
    assert Wsq
    if pow(Wsq,(ell-1)//2,ell)!=ell-1:continue
    c=min(s.sqrt_mod(Wsq*pow(nr,-1,ell)%ell,ell,all_roots=True))
    W=[int(c),0]
    assert R.mul(W,W)==[Wsq]
    P=(R.c(d*u0),R.mul(W,R.c(d*pow(169,-1,ell))));T=None
    Wlist=[];xs=[]
    for a in range(1,13):
        T=group(R,T,P);assert T
        x,y=T
        Wlist.append(R.mul(y,R.c(169*pow(d,-1,ell))))
        xs.append(x)
    assert group(R,T,P) is None
    B=R.mul(sum_ring(R,xs[:6]),R.c(pow(2*d,-1,ell)))
    Zs=read_Z(R,z,Wlist)
    assert len(B)<=1 and all(len(t)<=1 for t in Zs)
    for a,Z in enumerate(Zs,1):
        if Z==R.ev(G,B):
            matches[(tuple(B),tuple(Z))]=(u0,W,a)
assert len(matches)==1
(bb,zz),(ux,wx,a)=next(iter(matches.items()))
# Exact 3-adic formal point orbit, via Tate modulo 3^4.
R=Ring(3,4,[1,0,-1,-1]);mod=R.q
z=R.mul([1,0],[1,0])
for _ in range(3):
    z=R.sub(z,R.div(R.sub(R.pw(z,13),[1]),R.mul([13],R.pw(z,12))))
assert R.pw(z,13)==[1]
qT=(9*pow(35152,-1,mod))%mod
assert qT%9==0 and qT%27
# a4=-5qT mod(3^4), compare X coefficient after completing the square.
a4=(-5*qT)%mod
r0=next(r for r in range(0,mod,3)
    if (3*r*r+4*d*r-3*d*d-(4*(3*r+2*d))**2*a4)%mod==0)
U=next(u for u in range(1,mod,3) if (u*u-4*(3*r0+2*d))%mod==0)
X=[];W=[]
for a in range(1,13):
    t=R.pw(z,a);s0=R.sub([1],t);assert R.val(s0)==0
    x0=R.div(t,R.pw(s0,2))
    y0=R.div(R.pw(t,2),R.pw(s0,3))
    xx=R.add(x0,R.mul(R.c(qT),R.add(t,R.inv(t))))
    xx=R.sub(xx,R.c(2*qT))
    yy=R.add(y0,R.mul(R.c(qT),R.sub([1],R.inv(t))))
    x=R.add(R.mul(R.c(U**2),xx),R.c(r0))
    y=R.mul(R.c(U**3),R.add(yy,R.mul(R.c(pow(2,-1,mod)),xx)))
    assert R.mul(y,y)==R.mul(x,R.mul(R.sub(x,R.c(d)),R.add(x,R.c(3*d))))
    X.append(x);W.append(R.mul(y,R.c(169*pow(d,-1,mod))))
B=R.mul(R.c(pow(2*d,-1,mod)),sum_ring(R,X[:6]))
Z=read_Z(R,z,W)
assert len(B)<=1 and all(len(t)<=1 for t in Z)
res=[R.sub(zi,R.ev(G,B)) for zi in Z]
vals=[R.val(x) for x in res]
assert max(vals)<R.e and (sum(vals)-n['exact_small_rational_norm_factors']['3'])%3==0
v3=sum(v*pow(a,-1,13) for a,v in enumerate(vals,1))%13
print(json.dumps(dict(d=d,p5303=dict(u_in_unramified_quad=ux,W=wx,
      chosen_zeta_power=a,B=bb[0] if bb else 0,Z=zz[0] if zz else 0,test_rational_prime=ell),
      p3=dict(base_mod=mod,qT=qT,scaling_U=U,translate_R=r0,formal_B=B,
          formal_Z=Z,formal_gamma=res,free_orbit_normalized_valuations=vals,
          coefficient_on_e_xi_q3=v3)),
      sort_keys=True,indent=2))
