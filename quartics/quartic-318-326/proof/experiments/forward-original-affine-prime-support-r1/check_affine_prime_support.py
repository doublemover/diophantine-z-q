from math import prod,log
from itertools import product
from pathlib import Path
import sympy as S
checks={'prime_products':0,'log_divisor_bounds':0,'linear_bezout':0,'positive_eliminants':0,'axis_zero_cases':0,'exceptional_branches':0,'exceptional_prime_covers':0,'regular_prime_covers':0,'support_union_bounds':0}
def large(n,Y):return {int(p) for p in S.factorint(abs(n)) if p>Y}
def E(t,x,z,dx,dz):return (dx*z-dz*x)**2+t*t*dx*dx
def Q(a,b,c,d,e,f):return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
for n in list(range(-250,0))+list(range(1,251)):
 for Y in [2,3,5,11]:
  ps=large(n,Y)
  assert prod(ps)<=abs(n)
  assert Y**len(ps)<=abs(n)
  assert len(ps)*log(Y)<=log(abs(n))+1e-10
  checks['prime_products']+=1;checks['log_divisor_bounds']+=1
for t,x,z,dx,dz,h in product([-2,1],range(-2,3),range(-2,3),range(-2,3),range(-2,3),[-3,0,2]):
 ee=E(t,x,z,dx,dz)
 assert ee==dx*dx*((z+h*dz)**2+t*t)-(2*(dx*z-dz*x)*dz+dz*dz*(x+h*dx))*(x+h*dx)
 checks['linear_bezout']+=1
 if dx:
  assert ee>0;checks['positive_eliminants']+=1
 if not dx and dz:
  assert (ee==0)==(x==0);checks['axis_zero_cases']+=1
for k in [1,2]:
 for a in [(0,1,2),(1,-2,3),(2,1,-1)]:
  for d in [(1,0,1),(0,1,0),(2,-1,3),(0,0,1),(1,1,1)]:
   X,Z,W=a;dx,dz,dw=d
   for t in [-2,-1,1,3]:
    for h in range(-5,6):
     x,z,w=[aa+h*dd for aa,dd in zip(a,d)]
     for p in [2,3,5,7,11,13]:
      DD=(t*t+x*x)*(t*t+z*z)
      PP=k*(t+2)*w*w-2*x*z
      if t==-2 and t%p:
       assert (PP%p==0 and DD%p==0)==((x%p==0 and (t*t+z*z)%p==0) or (z%p==0 and (t*t+x*x)%p==0))
       checks['exceptional_branches']+=1
       if PP%p==0 and DD%p==0 and dx and dz:
        ee,ff=E(t,X,Z,dx,dz),E(t,Z,X,dz,dx)
        assert ee and ff
        assert p in large(ee,1)|large(ff,1)
        checks['exceptional_prime_covers']+=1
      for side in [False,True]:
       aa=k*(t+2)*dw*dw-2*dx*dz if side else k*dw*dw
       bb=2*k*(t+2)*W*dw-2*(X*dz+dx*Z) if side else 2*k*W*dw
       cc=k*(t+2)*W*W-2*X*Z if side else k*W*W+2*t
       ee=Q(aa,bb,cc,dx*dx,2*X*dx,X*X+t*t)
       ff=Q(aa,bb,cc,dz*dz,2*Z*dz,Z*Z+t*t)
       PP=k*(t+2)*w*w-2*x*z if side else k*w*w+2*t
       if ee and ff and p>2 and PP%p==0 and DD%p==0:
        assert p in large(ee,2)|large(ff,2)
        checks['regular_prime_covers']+=1
       if ee and ff:
        union=large(ee,2)|large(ff,2)
        assert len(union)*log(2)<=log(abs(ee))+log(abs(ff))+1e-10
        checks['support_union_bounds']+=1
# Zero eliminants must never be fed to the finite-prime argument.
assert E(-2,0,3,0,1)==0
# Divisibility does not bound number of h without a separate root/fiber argument.
assert all((0*h*h+0*h+0)%5==0 for h in range(-100,101))
for f in ['OriginalLargePrimeDivisorCount318','OriginalLinearNormEliminant318','OriginalExceptionalAffineElimination318','OriginalAffinePrimeSupport318']:
 s=(Path(__file__).parent/(f+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in s
print('PASS',checks,'zero-fiber and unlimited-h negative controls retained')
