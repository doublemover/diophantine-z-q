#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod, floor, isqrt
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import hermite_normal_form
checks={'whole_basis_pivots':0,'actual_nonzero_minor':0,'actual_leading_certificate':0,'affine_obstruction_divisibility':0,'eliminant_height':0}
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def mem(ps,k,ss,v):
 x,z,w=v
 return all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ss))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,v):return tuple(a*x for x in v)

a,b,c,d,e,f,h,n,r,ssym=S.symbols('a b c d e f h n r s')
def elim(a,b,c,d,e,f):return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
F=a*h*h+b*h+c;G=d*h*h+e*h+f
U=d*(a*e-b*d)*h-a*d*f+a*e*e-b*d*e+c*d*d
V=-a*(a*e-b*d)*h+a*a*f-a*b*e-a*c*d+b*b*d
assert S.expand(elim(a,b,c,d,e,f)-U*F-V*G)==0
assert S.expand(S.resultant(F,G,h)-elim(a,b,c,d,e,f))==0
middle=2*a*a*f*ssym-a*b*e*ssym-2*a*c*d*ssym-2*a*r*d*f+a*r*e*e+b*b*d*ssym-b*r*d*e+2*c*r*d*d
assert S.expand(elim(a,b*n,c*n*n+r,d,e*n,f*n*n+ssym)-elim(a,b,c,d,e,f)*n**4-middle*n*n-(a*ssym-r*d)**2)==0
k,t,dw,ew,dx,ex,dz,ez=S.symbols('k t dw ew dx ex dz ez')
assert S.expand(elim(k*dw*dw,2*k*dw*ew,k*ew*ew,dx*dx,2*dx*ex,ex*ex)-k*k*(dw*ex-dx*ew)**4)==0
for dd,ee in [(dx,ex),(dz,ez)]:
 assert S.expand(elim(k*(t+2)*dw*dw-2*dx*dz,2*k*(t+2)*dw*ew-2*(dx*ez+ex*dz),k*(t+2)*ew*ew-2*ex*ez,dd*dd,2*dd*ee,ee*ee)-k*k*(t+2)**2*(dw*ee-dd*ew)**4)==0
for ps in [(),(3,),(5,),(3,5)]:
 M=prod(ps)
 for k in [1,2]:
  for ss in product(*([None]+list(range(p)) for p in ps)):
   vs=sorted([v for v in product(range(-M,M+1),repeat=3) if v!=(0,0,0) and mem(ps,k,ss,v)],key=lambda v:dot(v,v))
   u=vs[0];v=next(v for v in vs if cross(u,v)!=(0,0,0));n=cross(u,v)
   w=next(w for w in vs if dot(n,w)!=0)
   residues=[v for v in product(range(M),repeat=3) if mem(ps,k,ss,v)]
   generators=residues+[(M,0,0),(0,M,0),(0,0,M)]
   H=hermite_normal_form(S.Matrix.hstack(*(S.Matrix(v) for v in generators)))
   assert abs(H.det())==M*M
   G=0;z=(0,0,0)
   for j in range(3):
    h=tuple(map(int,H[:,j]));value=dot(n,h)
    if not value:continue
    a,b,g=map(int,S.gcdex(G,value))
    z=add(scale(a,z),scale(b,h));G=g
   assert G>0 and dot(n,z)==G
   D=dot(n,n);uu=dot(u,u);vv=dot(v,v);uv=dot(u,v)
   A=Q(dot(u,z)*vv-dot(v,z)*uv,D);B=Q(dot(v,z)*uu-dot(u,z)*uv,D)
   za=add(add(z,scale(-floor(A+Q(1,2)),u)),scale(-floor(B+Q(1,2)),v))
   assert dot(n,za)==G and mem(ps,k,ss,za)
   C=S.Matrix.hstack(S.Matrix(u),S.Matrix(v),S.Matrix(za));Ci=C.inv()
   assert abs(C.det())==M*M
   assert dot(za,za)<=4*dot(w,w)
   assert uu<=vv<=dot(w,w) and 2*abs(uv)<=uu
   basis=[u,v,za];pivot=next(d for d in basis if d[2])
   checks['whole_basis_pivots']+=1
   for coord in [0,1]:
    off=next(e for e in basis if pivot[2]*e[coord]-pivot[coord]*e[2])
    delta=pivot[2]*off[coord]-pivot[coord]*off[2]
    assert delta!=0;checks['actual_nonzero_minor']+=1
    for t0 in [-3,-2,-1,1,3]:
     for side in [False,True]:
      if side and t0==-2:continue
      x,z,w=pivot;X,Z,W=off
      aa=k*(t0+2)*w*w-2*x*z if side else k*w*w
      bb=2*k*(t0+2)*w*W-2*(x*Z+X*z) if side else 2*k*w*W
      cc=k*(t0+2)*W*W-2*X*Z if side else k*W*W
      leading=elim(aa,bb,cc,pivot[coord]**2,2*pivot[coord]*off[coord],off[coord]**2)
      assert leading==k*k*(t0+2 if side else 1)**2*delta**4 and leading!=0
      checks['actual_leading_certificate']+=1
# Actual divisibility includes primes dividing quadratic leading coefficients.
for k,t0 in product([1,2,3],[-2,-1,1,3]):
 for offset in [(0,1,2),(1,-2,3),(2,1,-1)]:
  for direct in [(1,0,1),(0,1,0),(2,-1,3),(0,0,1)]:
   for hh in range(-4,5):
    x,z,w=[a+hh*b for a,b in zip(offset,direct)]
    X,Z,W=offset;dx,dz,dw=direct
    for side in [False,True]:
     PP=k*(t0+2)*w*w-2*x*z if side else k*w*w+2*t0
     DD=(t0*t0+x*x)*(t0*t0+z*z)
     aa=k*(t0+2)*dw*dw-2*dx*dz if side else k*dw*dw
     bb=2*k*(t0+2)*W*dw-2*(X*dz+dx*Z) if side else 2*k*W*dw
     cc=k*(t0+2)*W*W-2*X*Z if side else k*W*W+2*t0
     rr=[elim(aa,bb,cc,d*d,2*a*d,a*a+t0*t0) for a,d in [(X,dx),(Z,dz)]]
     for p in [2,3,5,7,11]:
      if PP%p==0 and DD%p==0:
       assert any(r%p==0 for r in rr);checks['affine_obstruction_divisibility']+=1
     for a,d in [(X,dx),(Z,dz)]:
      H=max(abs(aa),abs(bb),abs(cc));K=max(d*d,abs(2*a*d),a*a+t0*t0)
      assert abs(elim(aa,bb,cc,d*d,2*a*d,a*a+t0*t0))<=8*H*H*K*K
      checks['eliminant_height']+=1
# Negative: t=-2 destroys the claimed fourth coefficient for the second pair.
assert elim(0,0,0,1,0,0)==0
assert elim(0,0,1,0,0,1)==0 # Padding both constants to degree2 is degenerate.
for name in ['OriginalQuadraticEliminant318','OriginalAffineSieveEliminants318','OriginalEliminantLeadingTerm318','OriginalWholeBasisEliminants318']:
 text=(Path(__file__).parent/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'symbolic Bezout/resultant/scaled coefficient identities and two degeneracy controls')
