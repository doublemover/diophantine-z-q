"""Exact constant-conductor receiver back-map and universal cyclic p=29 gate."""
from fractions import Fraction as Q
from pathlib import Path
from math import prod
import json
pins=Path(__file__).resolve().parent.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json'
S=json.loads(pins.read_text())
R=S['R_input']; B=114444*R//(17*12**2); D0=1+114444*R
p=29
assert R==4376874610839020 and B==204618888056724185 and p*p==841
assert B==prod((5,11,17,163,661,733,1489,1861)) and B%24==17
assert D0%(p*p)==p*19 and R%p==26 and B%p==12
chi=lambda a:(lambda x: -1 if x==p-1 else x)(pow(a%p,(p-1)//2,p))
assert chi(2)==chi(-R)==chi(-B)==-1
def q(x,y=0):return x%p,y%p
def add(x,y):return q(x[0]+y[0],x[1]+y[1])
def sub(x,y):return q(x[0]-y[0],x[1]-y[1])
def mul(x,y):return q(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def sq(x):return mul(x,x)
def div(x,y):
 m=pow((y[0]*y[0]-2*y[1]*y[1])%p,-1,p)
 return mul(x,q(y[0]*m,-y[1]*m))
Z=q(0); F=sq(q(3,-1)); P0=(q(1,1),q(0,2))
def law(x):return mul(x,sub(sq(x),F))
def ga(P,T):
 if P is None:return T
 if T is None:return P
 x,y=P;u,v=T
 if x==u:
  if add(y,v)==Z:return
  assert y==v
  m=div(sub(mul(q(3),sq(x)),F),mul(q(2),y))
 else:m=div(sub(y,v),sub(x,u))
 X=sub(sub(sq(m),x),u); Y=sub(mul(m,sub(x,X)),y)
 assert sq(Y)==law(X)
 return X,Y
assert sq(P0[1])==law(P0[0])
orbit=[]; P=None
for j in range(1,21):
 P=ga(P,P0)
 if P is None:
  assert j==20
  orbit.append([j,"origin_U_zero"]); continue
 x,y=P; den=add(sq(x),F)
 if den==Z:
  assert y!=Z
  orbit.append([j,"U_pole"])
 else:
  val=sq(div(mul(q(2),y),den))
  assert val!=q(-R)
  orbit.append([j,val])
assert [j for j,x in orbit if x=="U_pole"]==[5,15]
assert {x for _,x in orbit if isinstance(x,tuple)}=={(0,0),(8,8),(15,15),(26,14),(27,19)}

# Arithmetic control only; the b is a rational square, not a linked pole.
beta=17;t=Q(6,251);u=beta*t*t
c0=10*t/(1+9*u); delta=1-beta*c0*c0; b=17*beta*c0*c0
theta=837821881
assert theta==prod((13,89,701,1033)) and delta==Q(theta,68509**2)
G=lambda v:1-beta*v*v
H=lambda v:1-9*beta*v*v
J=lambda v:1-81*beta*v*v
D=lambda v:beta*G(v)*H(v)
L=5*(9*u-1)/(1+9*u);z=-c0;e=Q(1)
V=G(t)*J(t)/(1+9*u)
assert L*L==25-9*beta*c0*c0 and beta*z*z+delta*e*e==1
assert L*L==16+9*delta*e*e and t==-z/(5-L) and V==10*delta*e/(5-L)
assert 0<b<17 and V*V==delta*G(t)*J(t)
h=V/(delta*G(t))
assert D(3*t)==D(t)*delta*h*h
assert D(3*t)>0 and D(t)>0 and h
d=beta*delta
Xk,Yk=delta/t**2,delta*V/t**3
assert Yk*Yk==Xk*(Xk-d)*(Xk-81*d)
def marked(v):
 A=1+3*beta*v*v; B0=4*beta*v; C=2*(1-3*beta*v*v)
 x,y=beta*A*A,beta*A*B0*C
 assert x-D(v)==B0*B0 and x+3*D(v)==beta*C*C and y
 assert y*y==x*(x-D(v))*(x+3*D(v))
 return A,x,y
a0,x0,y0=marked(t); a1,x1,y1=marked(3*t)
x1,y1=x1/h**2,y1/h**3
lam0,lam1=17*c0/a0,17*c0*h/a1
Bro=17*b
T=D(t)*lam0**2; s=Bro*lam0/lam1
y0,y1=y0*lam0**3,y1*(Bro*lam0)**3
sv=Bro*Bro*delta
assert s and y0 and y1
assert (y0*y0)==Bro*(Bro-T)*(Bro+3*T)
assert (y1*y1)==(Bro*s*s)*(Bro*s*s-T*sv)*(Bro*s*s+3*T*sv)

print(json.dumps({"fixed_actual_a0":{"p":p,"exact_orbit_order":20,"orbit_U_squared":orbit,
    "R":R,"beta":B,"normalizer_mod_p2":D0%(p*p),"char_minus_R":chi(-R),"char_minus_beta":chi(-B)},
    "toy_not_linked":{"beta":beta,"theta":theta,"b":str(b),"c_source":str(c0),"delta":str(delta),"L":str(L),"t":str(t),"t_prime":str(3*t),
                     "ratio_scale":str(h),"X_marked_constant_twist":str(Xk),"Y_marked_constant_twist":str(Yk),
                     "literal_s_nonzero":bool(s),"both_raw_cubic_identities_checked":True}},indent=2,sort_keys=True))
