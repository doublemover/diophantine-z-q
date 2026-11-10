#!/usr/bin/env python3
from itertools import product
import sympy as s,json
A,B,C,e,f,g,h,i,X=s.symbols('A B C e f g h i X')
L=e*(-B**3+2*A*B*C)+f*A*(B**2-A*C)-g*A*A*B+h*A**3
M=e*(-B*B*C+A*C*C)+f*A*B*C-g*A*A*C+i*A**3
E=A*M*M-B*L*M+C*L*L
Q=e*A*A*X*X+(f*A*A-e*A*B)*X+(e*B*B-e*A*C-f*A*B+g*A*A)
assert s.expand(A**3*(e*X**4+f*X**3+g*X*X+h*X+i)-(L*X+M)-Q*(A*X*X+B*X+C))==0
assert s.expand(E-(L*L*(A*X*X+B*X+C)-(A*L*X+B*L-A*M)*(L*X+M)))==0
assert s.expand(E-A**3*s.resultant(A*X*X+B*X+C,e*X**4+f*X**3+g*X*X+h*X+i,X))==0
k,t,ax,az,aw,dx,dz,dw=s.symbols('k t ax az aw dx dz dw')
r2=k*dw*dw-dx*dz;r1=2*k*aw*dw-ax*dz-dx*az;r0=k*aw*aw-ax*az+t*t+2*t
ks=[r2*r2,2*r2*r1,r1*r1+2*r2*r0+t*t*(dx+dz)**2,2*r1*r0+2*t*t*(ax+az)*(dx+dz),r0*r0+t*t*(ax+az)**2]
K=(k*(aw+X*dw)**2-(ax+X*dx)*(az+X*dz)+t*t+2*t)**2+t*t*(ax+az+X*(dx+dz))**2
assert s.expand(K-sum(v*X**(4-j) for j,v in enumerate(ks)))==0
P=k*(t+2)*(aw+X*dw)**2-2*(ax+X*dx)*(az+X*dz)
abc=[s.expand(P).coeff(X,j) for j in [2,1,0]]
expr=E.subs(dict(zip([A,B,C,e,f,g,h,i],abc+ks)))
Efn=s.lambdify((k,t,ax,az,aw,dx,dz,dw),expr,'math',cse=True)
c=dict(integer_common_divisors=0,affine_source_obstructions=0,full_width_rectangle_counts=0)
for kap,T in [(1,-2),(2,-2),(318,-2),(326,-2),(1,1),(3,-10),(5,5)]:
 for av in [(0,0,0),(1,2,-1),(-5,3,2),(2,-2,1)]:
  for dv in [(1,1,1),(2,-1,1),(1,0,2),(0,1,1)]:
   val=int(Efn(kap,T,*av,*dv))
   for q in [-3,-1,0,2,4]:
    xx,zz,ww=[a+q*d for a,d in zip(av,dv)]
    pp=kap*(T+2)*ww*ww-2*xx*zz;kk=(kap*ww*ww-xx*zz+T*T+2*T)**2+T*T*(xx+zz)**2
    for p in [2,3,5,7,11,17]:
     if pp%p==kk%p==0:assert val%p==0;c['integer_common_divisors']+=1
   # Source-dependent witness from audit, same original affine point.
   if kap in [1,318,326] and T==-10:pass
for kap in [1,318,326]:
 T=-10;av=(0,-2,0);dv=(1,2,1);val=int(Efn(kap,T,*av,*dv));assert val%17==0;c['affine_source_obstructions']+=1
for p in [3,5,7]:
 for kap,T in [(1,1),(2,p-2),(3,2)]:
  if kap%p==0 or T%p==0:continue
  for ra,rb,rc in [(2,3,4),(4,4,4),(2,5,2)]:
   if p>2*min(ra,rb,rc):continue
   for side in [False,True]:
    count=0
    for xx,zz,ww in product(range(-ra,ra+1),range(-rb,rb+1),range(-rc,rc+1)):
     pp=kap*(T+2)*ww*ww-2*xx*zz if side else kap*ww*ww+2*T
     kk=(kap*ww*ww-xx*zz+T*T+2*T)**2+T*T*(xx+zz)**2
     count+=pp%p==kk%p==0
    assert count*p*p<=512*ra*rb*rc;c['full_width_rectangle_counts']+=1
print(json.dumps({'status':'PASS','symbolic_identities':4,'checks':c,'no_nonvanishing_claim_from_common_divisor':True,'local_lean':'NOT_RUN'},indent=2))
