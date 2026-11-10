#!/usr/bin/env python3
import sympy as s,json
from itertools import product
k,t,ax,az,aw,dx,dz,dw,X=s.symbols('k t ax az aw dx dz dw X')
a=s.Matrix([ax,az,aw]);d=s.Matrix([dx,dz,dw])
F=k*(t+2)*(aw+X*dw)**2-2*(ax+X*dx)*(az+X*dz)
K=(k*(aw+X*dw)**2-(ax+X*dx)*(az+X*dz)+t*t+2*t)**2+t*t*(ax+az+X*(dx+dz))**2
A=s.expand(F).coeff(X,2)
Res=s.resultant(F,K,X);E=s.expand(A**3*Res)
assert s.expand(E.subs({ax:0,az:0,aw:0})-A**7*t**4*(t+2)**4)==0
U=k*k*(aw*dx-ax*dw)**4+4*dx*dx*(az*dx-ax*dz)**2
V=k*k*(aw*dz-az*dw)**4+4*dz*dz*(ax*dz-az*dx)**2
assert s.expand(E.subs(t,-2)+128*dx**3*dz**3*U*V)==0
vx,vz,vw=s.symbols('vx vz vw');v=s.Matrix([vx,vz,vw]);det=s.det(s.Matrix.hstack(a,v,d))
assert s.expand(dx*det+(az*dx-ax*dz)*(vx*dw-vw*dx)-(aw*dx-ax*dw)*(vx*dz-vz*dx))==0
assert s.expand(dz*det-(ax*dz-az*dx)*(vz*dw-vw*dz)-(aw*dz-az*dw)*(vx*dz-vz*dx))==0
Efn=s.lambdify((k,t,ax,az,aw,dx,dz,dw),E,'math',cse=True)
c=dict(regular_evaluation=0,exceptional_evaluation=0,same_index_shears=0,axis_positive=0)
for kap in [-3,1,2,318,326]:
 for T in [-5,-2,-1,1,3]:
  for q in [1,2,3]:
   u=(q,0,1);vv=(1,q,0);z0=(0,0,1)
   # det=q², representing original whole-basis index form.
   assert s.det(s.Matrix.hstack(s.Matrix(u),s.Matrix(vv),s.Matrix(z0)))==q*q
   for I,J in product(range(5),repeat=2):
    dd=tuple(z0[n]+I*u[n]+J*vv[n] for n in range(3))
    assert s.det(s.Matrix.hstack(s.Matrix(u),s.Matrix(vv),s.Matrix(dd)))==q*q;c['same_index_shears']+=1
    lead=kap*(T+2)*dd[2]**2-2*dd[0]*dd[1]
    if not lead:continue
    if T!=-2:
     val=int(Efn(kap,T,0,0,0,*dd));assert val==lead**7*T**4*(T+2)**4 and val!=0;c['regular_evaluation']+=1
    else:
     val=int(Efn(kap,T,*u,*dd));assert val!=0;c['exceptional_evaluation']+=1
     xx,zz,ww=u;DX,DZ,DW=dd
     uval=kap*kap*(ww*DX-xx*DW)**4+4*DX*DX*(zz*DX-xx*DZ)**2
     vval=kap*kap*(ww*DZ-zz*DW)**4+4*DZ*DZ*(xx*DZ-zz*DX)**2
     assert uval>0 and vval>0;c['axis_positive']+=2
     assert val==-128*DX**3*DZ**3*uval*vval
print(json.dumps({'status':'PASS','symbolic_identities':4,'checks':c,'local_lean':'NOT_RUN','no_generic_position_input':True},indent=2))
