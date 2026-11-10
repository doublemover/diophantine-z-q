from itertools import product
from math import gcd, log
import sympy as s
checks=dict(actual_fiber_points=0,regular_log_tails=0,exceptional_log_tails=0,offset_evaluations=0,offset_zero_counts=0,zero_cylinders=0,sheared_transverse=0)
def E(a,b,c,d,e,f):return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
def coeff(side,k,t,a,d):
 x,z,w=a;dx,dz,dw=d
 return ((k*(t+2)*dw*dw-2*dx*dz,2*k*(t+2)*w*dw-2*(x*dz+dx*z),k*(t+2)*w*w-2*x*z)
         if side else (k*dw*dw,2*k*w*dw,k*w*w+2*t))
def es(side,k,t,a,d,c):
 x=a[c];dx=d[c]
 return E(*coeff(side,k,t,a,d),dx*dx,2*x*dx,x*x+t*t)
def lin(t,x,z,dx,dz):return (dx*z-dz*x)**2+t*t*dx*dx
def factors(n):
 assert n
 return {int(p) for p in s.factorint(abs(n))}
def point_primes(side,k,t,a,d,h):
 x,z,w=[a[i]+h*d[i] for i in range(3)]
 F=k*(t+2)*w*w-2*x*z if side else k*w*w+2*t
 D=(t*t+x*x)*(t*t+z*z)
 return factors(gcd(F,D))
for side,k,t,a,d,B,Y in product([False,True],[1,2],[-2,-1,1,2],[(0,1,0),(1,-2,3),(2,1,-1)],[(1,1,1),(0,1,2),(2,-1,1)], [1,3], [2,5]):
 aa=coeff(side,k,t,a,d)[0]
 bad=[h for h in range(-B,B+1) if any(p>Y and p>2*B and aa%p for p in point_primes(side,k,t,a,d,h))]
 n,m=es(side,k,t,a,d,0),es(side,k,t,a,d,1)
 if n and m:
  support={p for p in factors(n)|factors(m) if p>Y}
  for h in bad:
   witness={p for p in point_primes(side,k,t,a,d,h) if p>Y and p>2*B and aa%p}
   assert witness<=support
  assert len(bad)<=2*len(support)
  assert len(bad)*log(Y)<=2*(log(abs(n))+log(abs(m)))+1e-10
  checks['regular_log_tails']+=1
  checks['actual_fiber_points']+=len(bad)
 if side and t==-2 and d[0] and d[1]:
  n,m=lin(t,a[0],a[1],d[0],d[1]),lin(t,a[1],a[0],d[1],d[0])
  assert n>0 and m>0
  support={p for p in factors(n)|factors(m) if p>Y}
  assert len(bad)<=2*len(support)
  assert len(bad)*log(Y)<=2*(log(n)+log(m))+1e-10
  checks['exceptional_log_tails']+=1
# Universal actual offset polynomial, grading, and axis restriction.
i,j,n,k,t=s.symbols('i j n k t');u=s.symbols('ux uz uw');v=s.symbols('vx vz vw');d=s.symbols('dx dz dw')
a=[i*u[r]+j*v[r] for r in range(3)]
for side,c in product([False,True],[0,1]):
 p=s.Poly(s.expand(es(side,k,t,a,d,c)),i,j)
 assert p.total_degree()<=4
 for axis,e in [(j,u),(i,v)]:
  actual=s.expand(p.as_expr().subs({axis:0,(i if axis==j else j):n}))
  scaled=s.expand(es(side,k,t,[n*x for x in e],d,c))
  assert s.expand(actual-scaled)==0
# Same bounded shear, actual minor and actual zero-locus cylinders.
for u,v,z in [((1,0,0),(0,1,0),(0,0,1)),((2,0,0),(0,3,0),(1,1,2)),((1,0,1),(0,1,1),(0,0,1))]:
 assert s.det(s.Matrix.hstack(*[s.Matrix(x) for x in (u,v,z)]))
 for I,J in product(range(5),repeat=2):
  d=tuple(z[r]+I*u[r]+J*v[r] for r in range(3))
  if not d[2]:continue
  for c in [0,1]:
   assert any(d[2]*e[c]-d[c]*e[2] for e in (u,v))
   checks['sheared_transverse']+=1
  for side,k,t in product([False,True],[1,2],[-2,1,2]):
   if side and t==-2:continue
   for A,B,C in [(2,3,1),(5,8,2)]:
    zero=[set(),set()]
    for ii,jj in product(range(-A,A+1),range(-B,B+1)):
     a=[ii*u[r]+jj*v[r] for r in range(3)]
     for c in [0,1]:
      if es(side,k,t,a,d,c)==0:zero[c].add((ii,jj))
      checks['offset_evaluations']+=1
    for zz in zero:
     assert len(zz)<=4*((2*A+1)+(2*B+1))
     checks['offset_zero_counts']+=1
    both=zero[0]|zero[1]
    assert len(both)*(2*C+1)<=8*((2*A+1)+(2*B+1))*(2*C+1)
    checks['zero_cylinders']+=1
# Negative control: actual eliminant zero values really occur.
assert es(False,1,2,(0,0,0),(1,0,1),0)==0
print('PASS',checks,'universal degree4 and axis identities; actual zero-eliminant negative control retained')
