import sys,json
from functools import reduce
from pathlib import Path
from hashlib import sha256
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
S=Path(sys.argv[1])
def read(p,h):
 f=(S/p).read_bytes(); assert sha256(f).hexdigest()==h
 return json.loads(f)
j=read('actual-one-I-ordinary-q53-ideal-r1/EXACT-ORDINARY-Q53-IDEAL-AND-PRINCIPAL-CHART.json','f5e25122b2b58fe2d14ab66aa1bc61992a6446df8d3b4603e460129030da3dc2')
k=read('actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json','7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a')
n=read('actual-one-I-q53-global-norm-r1/ACTUAL-Q53-GLOBAL-PRINCIPAL-NORM.json','31adfcc272aaf806a8cb3838ff58b7d33f5ab3fc1e94dbfd9ad043b79d445079')
D=k['d']; assert D==j['d']==n['d']
u=s.symbols('u')
for p in (53,131,157,313,521,547,677):
 assert s.isprime(p) and p%13==1 and D%p
 F=s.Poly.from_list(k['x_root_poly_coefficients'],u,modulus=p)
 fac=F.factor_list()[1]; assert sum(q.degree() for q,m in fac)==84 and all(m==1 for q,m in fac)
 z=next(x for a in range(2,p) if (x:=pow(a,(p-1)//13,p))!=1)
 assert pow(z,13,p)==1
 result=1
 for q,m in fac:
  poly=[int(c)%p for c in q.monic().all_coeffs()]
  Q=p**q.degree()
  A=lambda x,y:g.gf_add(x,y,p,ZZ)
  S=lambda x,y:g.gf_sub(x,y,p,ZZ)
  M=lambda x,y:g.gf_rem(g.gf_mul(x,y,p,ZZ),poly,p,ZZ)
  C=lambda x:[x%p] if x%p else []
  P=lambda x,e:g.gf_pow_mod(x,e,poly,p,ZZ)
  I=lambda x:P(x,Q-2) if x else (_ for _ in ()).throw(Exception('zero inverse'))
  x=g.gf_rem([D%p,0],poly,p,ZZ)
  F=M(M(x,S(x,C(D))),A(x,C(3*D)))
  # Represent y_a=c_a y_1. Addition slopes then equal c_m y_1.
  X,CY=x,C(1); xs=[X]; ys=[CY]
  for a in range(1,6):
   if a==1:
    CM=M(A(A(M(C(3),M(X,X)),M(C(4*D),X)),C(-3*D*D)),I(M(C(2),F)))
   else:
    CM=M(S(CY,C(1)),I(S(X,x)))
   Z=S(S(S(M(M(CM,CM),F),C(2*D)),x),X)
   CY=S(M(CM,S(x,Z)),C(1)); X=Z
   xs.append(X); ys.append(CY)
   assert M(M(CY,CY),F)==M(M(X,S(X,C(D))),A(X,C(3*D)))
  B=M(reduce(A,xs,[]),C(pow(2*D,-1,p)))
  Zunit=M(reduce(A,(M(C(pow(z,a,p)-pow(z,-a,p)),Y) for a,Y in enumerate(ys,1)),[]),C(169*pow(D,-1,p)))
  G=[]
  for c in j['Z_equals_G_of_B_desc']:G=A(M(G,B),C(c))
  N=P(S(M(G,G),M(M(Zunit,Zunit),F)),(Q-1)//(p-1))
  assert len(N)<=1
  result=result*(N[0] if N else 0)%p
 assert result==n['norm_signed']%p,(p,result,n['norm_signed']%p)
 print(p,[q.degree() for q,m in fac],result)
