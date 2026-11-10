#!/usr/bin/env python3
import sympy as s,mpmath as mp,json
from itertools import product
mp.mp.dps=60
I,J,H=s.symbols('I J H')
def elim(k,t,a,d):
 ax,az,aw=a;dx,dz,dw=d
 A=k*(t+2)*dw*dw-2*dx*dz;B=2*k*(t+2)*aw*dw-2*(ax*dz+dx*az);C=k*(t+2)*aw*aw-2*ax*az
 r2=k*dw*dw-dx*dz;r1=2*k*aw*dw-ax*dz-dx*az;r0=k*aw*aw-ax*az+t*t+2*t
 e=r2*r2;f=2*r2*r1;g=r1*r1+2*r2*r0+t*t*(dx+dz)**2;h=2*r1*r0+2*t*t*(ax+az)*(dx+dz);ii=r0*r0+t*t*(ax+az)**2
 L=e*(-B**3+2*A*B*C)+f*A*(B*B-A*C)-g*A*A*B+h*A**3
 M=e*(-B*B*C+A*C*C)+f*A*B*C-g*A*A*C+ii*A**3
 return A*M*M-B*L*M+C*L*L

def obstruction(k,t,a,d,h,p):
 x,z,w=[a[j]+h*d[j] for j in range(3)]
 return (k*(t+2)*w*w-2*x*z)%p==0 and ((k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2)%p==0
c=dict(actual_degree=0,offset_zero_counts=0,actual_integer_fibers=0,rectangle_tail=0,zero_cylinders=0)
for k,t in [(1,-2),(2,-2),(318,-2),(326,-2),(1,1),(3,-10),(5,5)]:
 for q in [1,2]:
  u=(q,0,1);v=(1,q,0);base=(0,0,1)
  for ii,jj in [(1,1),(2,1),(0,2)]:
   d=tuple(base[n]+ii*u[n]+jj*v[n] for n in range(3))
   lead=k*(t+2)*d[2]**2-2*d[0]*d[1]
   if not lead:continue
   pol=s.Poly(s.expand(elim(k,t,tuple(I*u[n]+J*v[n] for n in range(3)),d)),I,J)
   assert not pol.is_zero and pol.total_degree()<=8;c['actual_degree']+=1
   for A,B,C,Y in [(1,2,1,2),(2,1,2,3)]:
    offsets=[tuple(i*u[n]+j*v[n] for n in range(3)) for i,j in product(range(-A,A+1),range(-B,B+1))]
    vals=[int(elim(k,t,a,d)) for a in offsets]
    zeros=sum(e==0 for e in vals);assert zeros<=8*((2*A+1)+(2*B+1));c['offset_zero_counts']+=1
    assert zeros*(2*C+1)<=8*((2*A+1)+(2*B+1))*(2*C+1);c['zero_cylinders']+=1
    N=1+sum(abs(e) for e in vals)
    total=0
    for a,e in zip(offsets,vals):
     if not e:
      # Full cylinder retained; this dominates every true obstruction point there.
      total+=2*C+1;continue
     ps=[int(p) for p in s.factorint(abs(e)) if p>Y and p>2*C and lead%p]
     count=sum(any(obstruction(k,t,a,d,h,p) for p in ps) for h in range(-C,C+1))
     assert mp.mpf(count)*mp.log(Y)<=2*mp.log(abs(e))+mp.mpf('1e-50')
     total+=count;c['actual_integer_fibers']+=1
    rhs=(2*A+1)*(2*B+1)*2*mp.log(N)+8*((2*A+1)+(2*B+1))*(2*C+1)*mp.log(Y)
    assert total*mp.log(Y)<=rhs;c['rectangle_tail']+=1
print(json.dumps({'status':'PASS','checks':c,'precision_digits':60,'actual_quartic_zero_cylinders_retained':True,'local_lean':'NOT_RUN'},indent=2))
