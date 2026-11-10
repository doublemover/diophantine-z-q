from itertools import product
from functools import lru_cache
from math import gcd,log,sqrt
import sympy as s
checks=dict(coefficient_budgets=0,regular_heights=0,exceptional_heights=0,frame_boxes=0,original_points=0,same_point_covers=0,covered_rectangle_counts=0,full_tail_bounds=0)
def E(a,b,c,d,e,f):return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
def coeff(side,k,t,a,d):
 x,z,w=a;dx,dz,dw=d
 return ((k*(t+2)*dw*dw-2*dx*dz,2*k*(t+2)*w*dw-2*(x*dz+dx*z),k*(t+2)*w*w-2*x*z)
         if side else (k*dw*dw,2*k*w*dw,k*w*w+2*t))
def es(side,k,t,a,d,c):
 x=a[c];dx=d[c]
 return E(*coeff(side,k,t,a,d),dx*dx,2*x*dx,x*x+t*t)
def lin(t,x,z,dx,dz):return (dx*z-dz*x)**2+t*t*dx*dx
def height(k,t,L):
 H=(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t)
 K=2*L*L+t*t
 return H,K,8*H*H*K*K,4*L**4+t*t*L*L
for L in range(1,4):
 for k,t,a,d in product([-2,1,3],[-2,-1,1,2],[(L,0,-L),(-L,L,L),(0,0,0)],[(L,L,0),(0,-L,L),(-L,-L,-L)]):
  H,K,R,Q=height(k,t,L)
  for side in [False,True]:
   assert all(abs(c)<=H for c in coeff(side,k,t,a,d))
   checks['coefficient_budgets']+=1
   for c in [0,1]:
    x,dx=a[c],d[c]
    assert max(dx*dx,abs(2*x*dx),x*x+t*t)<=K
    assert abs(es(side,k,t,a,d,c))<=R
    checks['regular_heights']+=1
  assert abs(lin(t,a[0],a[1],d[0],d[1]))<=Q
  checks['exceptional_heights']+=1
@lru_cache(None)
def factors(n):
 assert n
 return tuple(map(int,s.factorint(abs(n))))
def ptps(side,k,t,y):
 x,z,w=y
 P=k*(t+2)*w*w-2*x*z if side else k*w*w+2*t
 D=(t*t+x*x)*(t*t+z*z)
 return factors(gcd(P,D))
def comb(u,v,z,a,b,c):return tuple(a*u[r]+b*v[r]+c*z[r] for r in range(3))
def shear(u,v,z,i,j):return comb(u,v,z,i,j,1)
for u,v,w,z in [((1,0,0),(0,1,0),(0,0,1),(0,0,1)),((1,0,0),(0,2,0),(0,0,3),(1,1,3))]:
 W=sqrt(sum(x*x for x in w));M=abs(int(s.det(s.Matrix.hstack(*[s.Matrix(y) for y in (u,v,z)]))))
 for A,B,C in [(1,2,1),(2,2,1)]:
  AA,BB=A+4*C,B+4*C;L=(AA+BB+10)*W
  for i,j in product(range(5),repeat=2):
   d=shear(u,v,z,i,j)
   assert max(map(abs,d))<=L+1e-10
   for a,b in product(range(-AA,AA+1),range(-BB,BB+1)):
    off=comb(u,v,z,a,b,0)
    assert max(map(abs,off))<=L+1e-10
    checks['frame_boxes']+=1
  for side,k,t in product([False,True],[1,2],[-2,1,2]):
   Y=2;original=[];images=set()
   eligible=[(i,j) for i,j in product(range(5),repeat=2) if (d:=shear(u,v,z,i,j))[2] and (t!=-2 or (d[0] and d[1]))]
   assert len(eligible)<=25
   for abc in product(range(-A,A+1),range(-B,B+1),range(-C,C+1)):
    y=comb(u,v,z,*abc);checks['original_points']+=1
    ps=[p for p in ptps(side,k,t,y) if p>=5 and p>Y and p>2*C and k%p and M%p]
    if not ps:continue
    p=ps[0];original.append(abc)
    ij=next((i,j) for i,j in product(range(5),repeat=2) if all(coeff(ss,k,t,(0,0,0),shear(u,v,z,i,j))[0]%p for ss in [False,True]))
    assert ij in eligible
    i,j=ij;a,b,c=abc;aa,bb=a-i*c,b-j*c;d=shear(u,v,z,i,j)
    assert abs(aa)<=AA and abs(bb)<=BB
    assert comb(u,v,d,aa,bb,c)==y
    assert coeff(side,k,t,(0,0,0),d)[0]%p
    images.add((i,j,aa,bb,c));checks['same_point_covers']+=1
   assert len(images)==len(original)
   _,_,R,Q=height(k,t,L);N=1+R+Q
   H=(2*AA+1)*(2*BB+1)*4*log(N)+8*((2*AA+1)+(2*BB+1))*(2*C+1)*log(Y)
   total=0
   for i,j in eligible:
    d=shear(u,v,z,i,j);lead=coeff(side,k,t,(0,0,0),d)[0];count=0
    for a,b,c in product(range(-AA,AA+1),range(-BB,BB+1),range(-C,C+1)):
     y=comb(u,v,d,a,b,c)
     if any(p>Y and p>2*C and lead%p for p in ptps(side,k,t,y)):count+=1
    assert count*log(Y)<=H+1e-8
    total+=count;checks['covered_rectangle_counts']+=1
   assert len(original)<=total
   assert len(original)*log(Y)<=25*H+1e-8
   checks['full_tail_bounds']+=1
print('PASS',checks,'original point/prime quantifier order, fixed25 collection, t=-2, exact same-point inverse')
