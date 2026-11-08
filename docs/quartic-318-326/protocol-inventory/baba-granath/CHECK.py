"""Exact rational identities only; not a PEL/Jacobian identification checker."""
from fractions import Fraction as F
import json, platform
import sympy as s
bits=[(0,0),(1,0),(0,1),(1,1)]
def mul(x,y):
 out=[F(0)]*4
 for p,(a,b) in enumerate(bits):
  for q,(c,d) in enumerate(bits):
   out[bits.index(((a+c)%2,(b+d)%2))]+=x[p]*y[q]*(-1)**(b*c)*2**((a+c)//2)*(-3)**((b+d)//2)
 return out
def bar(x): return [x[0]]+[-a for a in x[1:]]
def tr(x): return 2*x[0]
b=[[F(1),0,0,0],[0,F(1),0,0],[F(1,2),0,F(1,2),0],[0,F(1,2),0,F(1,2)]]
mu=[0,0,F(2),F(1)]; inv=[-x/F(6) for x in mu]
M=s.Matrix([[tr(mul(mul(inv,x),bar(y))) for y in b] for x in b])
N=s.Matrix([[tr(mul(mul(bar(x),mu),y)) for y in b] for x in b])
assert mul(mu,mu)==[-6,0,0,0] and M.det()==1 and N==6*M and N.det()==1296
u=s.symbols('u'); f=u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60);g=7*u*u+300*u+3600
hs=[u*u-60*u-1800,13*u*u+480*u+3600,11*u*u+600*u+7200];h=s.prod(hs)
assert s.expand(g**6-97200*f**2-h**2)==0
polys={'F':f,'G':g,'H':h}
factors={n:{str(p):int(e) for p,e in s.factorint(abs(s.discriminant(q,u))).items()} for n,q in polys.items()}
res={a+b:{str(p):int(e) for p,e in s.factorint(abs(s.resultant(polys[a],polys[b],u))).items()} for a,b in [('F','G'),('F','H'),('G','H')]}
assert all(int(p)<=13 for d in list(factors.values())+list(res.values()) for p in d)
forms=[(0,1),(1,0),(1,-1),(1,-2401),(32,343)]
dets=[abs(a*d-b*c) for k,(a,b) in enumerate(forms) for c,d in forms[k+1:]]
assert all(x!=0 for x in dets)
support=sorted({int(p) for d in dets for p in s.factorint(d)})
assert support==[2,3,5,7]
print(json.dumps({'python':platform.python_version(),'sympy':s.__version__,'status':'PASS','scope':'finite rational arithmetic only','primitive_matrix':[[int(a) for a in row] for row in M.tolist()],'primitive_determinant':int(M.det()),'published_form_scalar':6,'published_form_determinant':int(N.det()),'pullback_identity':True,'discriminants':factors,'pairwise_resultants':res,'H_factor_discriminants':[int(s.discriminant(q,u)) for q in hs],'J_at_infinity':str(s.Rational(-57600,7**6)),'five_contact_determinants':dets,'five_contact_support':support},indent=2))
