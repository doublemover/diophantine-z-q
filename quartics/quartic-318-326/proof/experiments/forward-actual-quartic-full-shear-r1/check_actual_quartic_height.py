#!/usr/bin/env python3
from itertools import product
import json,random,runpy
# Pure exact arithmetic. Do not import/run Lean or any compiler.
random.seed(318326)
def coeff(k,t,a,d):
 ax,az,aw=a;dx,dz,dw=d
 A=k*(t+2)*dw*dw-2*dx*dz;B=2*k*(t+2)*aw*dw-2*(ax*dz+dx*az);C=k*(t+2)*aw*aw-2*ax*az
 r2=k*dw*dw-dx*dz;r1=2*k*aw*dw-ax*dz-dx*az;r0=k*aw*aw-ax*az+t*t+2*t
 ks=[r2*r2,2*r2*r1,r1*r1+2*r2*r0+t*t*(dx+dz)**2,2*r1*r0+2*t*t*(ax+az)*(dx+dz),r0*r0+t*t*(ax+az)**2]
 return (A,B,C,*ks),(r2,r1,r0)
def elimination(cs):
 a,b,c,e,f,g,h,i=cs
 L=e*(-b**3+2*a*b*c)+f*a*(b*b-a*c)-g*a*a*b+h*a**3
 M=e*(-b*b*c+a*c*c)+f*a*b*c-g*a*a*c+i*a**3
 return a*M*M-b*L*M+c*L*L,L,M
counts=dict(generic_remainder=0,generic_eliminant=0,actual_inner=0,actual_quartic_coefficients=0,actual_eliminant_height=0,constructed_rectangle_height=0,fixed_shear_same_points=0)
for _ in range(2000):
 H=random.randint(0,12);cs=[random.randint(-H,H) for _ in range(8)]
 E,L,M=elimination(cs)
 assert abs(L)<=7*H**4 and abs(M)<=5*H**4;counts['generic_remainder']+=1
 assert abs(E)<=109*H**9;counts['generic_eliminant']+=1
for k,t in product([-3,1,2,318,326],[-10,-2,-1,1,3]):
 for LL in [0,1,2,5]:
  for _ in range(12):
   a=tuple(random.randint(-LL,LL) for _ in range(3));d=tuple(random.randint(-LL,LL) for _ in range(3))
   cs,rs=coeff(k,t,a,d);J=(2*abs(k)+2)*LL**2+t*t+2*abs(t);Q=8*(J*J+t*t*LL*LL)
   F=(2*abs(k)*(abs(t)+2)+4)*LL*LL+2*abs(t);H=1+F+Q
   assert all(abs(r)<=J for r in rs);counts['actual_inner']+=3
   assert all(abs(v)<=Q for v in cs[3:]);counts['actual_quartic_coefficients']+=5
   assert all(abs(v)<=H for v in cs)
   assert abs(elimination(cs)[0])<=109*H**9;counts['actual_eliminant_height']+=1
# Actual fixed candidate maps restore the same integer coefficients, not just same residue.
for A,B,C in [(1,2,1),(2,1,2),(2,2,2)]:
 for i,j in product(range(5),repeat=2):
  for a,b,c in product(range(-A,A+1),range(-B,B+1),range(-C,C+1)):
   r=(a-i*c,b-j*c,c)
   assert abs(r[0])<=A+4*C and abs(r[1])<=B+4*C
   assert (r[0]+i*r[2],r[1]+j*r[2],r[2])==(a,b,c);counts['fixed_shear_same_points']+=1
for k,t in [(1,-2),(318,-2),(326,-10),(2,1)]:
 u=(1,0,1);v=(1,1,0);z=(0,0,1)
 for i,j in [(1,1),(2,3),(4,0)]:
  d=tuple(z[n]+i*u[n]+j*v[n] for n in range(3));A,B=2,3
  offsets=[tuple(a*u[n]+b*v[n] for n in range(3)) for a,b in product(range(-A,A+1),range(-B,B+1))]
  LL=max(abs(x) for vec in offsets+[d] for x in vec)
  J=(2*abs(k)+2)*LL**2+t*t+2*abs(t);Q=8*(J*J+t*t*LL*LL)
  F=(2*abs(k)*(abs(t)+2)+4)*LL*LL+2*abs(t);H=1+F+Q
  N=1+sum(abs(elimination(coeff(k,t,a,d)[0])[0]) for a in offsets)
  assert N<=1+(2*A+1)*(2*B+1)*109*H**9;counts['constructed_rectangle_height']+=1
counts['actual_successful_shear_points']=0
for prime in [5,7,11]:
 for kap,T in [(1,-2),(318,-2),(326,-10),(2,1)]:
  if kap%prime==0:continue
  for q in [1,2,3]:
   if q%prime==0:continue
   u=(q,0,1);v=(1,q,0);z=(0,0,1)
   for a,b,c in product(range(-2,3),repeat=3):
    y=tuple(a*u[n]+b*v[n]+c*z[n] for n in range(3));xx,zz,ww=y
    if (kap*(T+2)*ww*ww-2*xx*zz)%prime or ((kap*ww*ww-xx*zz+T*T+2*T)**2+T*T*(xx+zz)**2)%prime:continue
    chosen=None
    for ii,jj in product(range(5),repeat=2):
     d=tuple(z[n]+ii*u[n]+jj*v[n] for n in range(3))
     if (kap*(T+2)*d[2]**2-2*d[0]*d[1])%prime:
      chosen=ii,jj,d;break
    assert chosen is not None
    ii,jj,d=chosen;r=(a-ii*c,b-jj*c,c)
    assert tuple(r[0]*u[n]+r[1]*v[n]+r[2]*d[n] for n in range(3))==y
    counts['actual_successful_shear_points']+=1
print(json.dumps({'status':'PASS','exact_checks':counts,'local_lean':'NOT_RUN','no_sampled_height_used_as_proof':True},indent=2))
