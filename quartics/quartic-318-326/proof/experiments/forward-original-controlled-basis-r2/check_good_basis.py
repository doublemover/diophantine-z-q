#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod, floor
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import hermite_normal_form
checks={'whole_lattice_bases':0,'integral_coordinate_checks':0,'plane_saturation':0,'controlled_lengths':0,'nonprimitive_negative':0}
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def mem(ps,k,ss,v):
 x,z,w=v
 return all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ss))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,v):return tuple(a*x for x in v)
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
   checks['whole_lattice_bases']+=1;checks['controlled_lengths']+=1
   for y in generators+vs[:60]:
    coeff=Ci*S.Matrix(y)
    assert all(c.q==1 for c in coeff)
    checks['integral_coordinate_checks']+=1
    if dot(n,y)==0:
     assert coeff[2]==0;checks['plane_saturation']+=1
   Cbad=S.Matrix.hstack(S.Matrix(scale(2,u)),S.Matrix(v),S.Matrix(za))
   assert abs(Cbad.det())==2*M*M and (Cbad.inv()*S.Matrix(u))[0]==S.Rational(1,2)
   checks['nonprimitive_negative']+=1
for name in ['OriginalReducedBasisData318','OriginalSaturatedPlane318','OriginalControlledIntegralBasis318']:
 text=(Path(__file__).resolve().parent/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'negative: independent proper sublattice fails integral spanning')
