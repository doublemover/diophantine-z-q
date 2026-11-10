#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod, floor, isqrt
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import hermite_normal_form
checks={'collected_coefficients':0,'degree_bounds':0,'row_weight_bounds':0,'residue_inverse':0,'content_witness':0,'same_basis_coprime':0,'complementary_minimum':0,'basis_covolume':0,'good_volume_count':0,'hadamard_minima':0,'determinant_minima':0,'reciprocal_minima':0,'cofactor_inverse':0,'anisotropic_bounds':0,'rectangle_count':0,'weight_transport':0,'whole_lattice_bases':0,'integral_coordinate_checks':0,'plane_saturation':0,'controlled_lengths':0,'nonprimitive_negative':0}
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
   determinant=int(C.det())
   cofs=[cross(v,za),cross(za,u),cross(u,v)]
   assert abs(determinant)==M*M
   checks['basis_covolume']+=1
   assert determinant*determinant<=4*dot(u,u)*dot(v,v)*dot(w,w)
   checks['hadamard_minima']+=1
   R0=isqrt(dot(w,w))
   if R0*R0<dot(w,w):R0+=1
   for TT in [max(0,R0-1),R0]:
    small=[y for y in vs if dot(y,y)<=TT*TT]
    rank=S.Matrix.hstack(*(S.Matrix(y) for y in small)).rank() if small else 0
    assert (rank==3)==(dot(w,w)<=TT*TT)
    checks['complementary_minimum']+=1
   for Rbig in [R0,R0+1]:
    pointsbig=[y for y in product(range(-Rbig,Rbig+1),repeat=3) if dot(y,y)<=Rbig*Rbig and mem(ps,k,ss,y)]
    assert len(pointsbig)*M*M<=5202*Rbig**3
    checks['good_volume_count']+=1
   assert dot(u,u)*dot(v,v)*dot(w,w)<=16*determinant*determinant
   checks['determinant_minima']+=1
   for y in generators+vs[:60]:
    coeff=tuple(map(int,Ci*S.Matrix(y)))
    assert tuple(dot(n,y) for n in cofs)==tuple(determinant*c for c in coeff)
    checks['cofactor_inverse']+=1
    lengths=[dot(v,v)*dot(za,za),dot(za,za)*dot(u,u),dot(u,u)*dot(v,v)]
    for c,length in zip(coeff,lengths):
     assert c*c*determinant*determinant<=dot(y,y)*length
     checks['anisotropic_bounds']+=1
   for R in [0,1,2,3]:
    points=[y for y in product(range(-R,R+1),repeat=3) if dot(y,y)<=R*R and mem(ps,k,ss,y)]
    lengths=[dot(v,v)*dot(za,za),dot(za,za)*dot(u,u),dot(u,u)*dot(v,v)]
    radii=[isqrt((R*R*length)//(determinant*determinant)) for length in lengths]
    coords=[tuple(map(int,Ci*S.Matrix(y))) for y in points]
    assert len(set(coords))==len(points)
    assert all(all(abs(c)<=a for c,a in zip(cs,radii)) for cs in coords)
    assert len(points)<=prod(2*a+1 for a in radii)
    minradii=[isqrt((64*R*R)//dot(u,u)),isqrt((64*R*R)//dot(v,v)),isqrt((16*R*R)//dot(w,w))]
    assert all(a<=b for a,b in zip(radii,minradii))
    assert len(points)<=prod(2*a+1 for a in minradii)
    checks['reciprocal_minima']+=1
    checks['rectangle_count']+=1
    weight=lambda y:1+sum(a*a for a in y)
    assert sum(weight(y) for y in points)==sum(weight(tuple(C*S.Matrix(c))) for c in coords)
    checks['weight_transport']+=1
   H2=36*dot(w,w)
   for i in range(3):
    wwgt=sum(abs(int(C[i,j])) for j in range(3))
    assert wwgt*wwgt<=H2
    checks['row_weight_bounds']+=1
   xx,zz,ww=S.symbols('xx zz ww');xs,zs,ws=C*S.Matrix([xx,zz,ww])
   for label in [1,-2,3]:
    forms=[k*ws*ws+2*label,k*(label+2)*ws*ws-2*xs*zs,
      (label*label+xs*xs)*(label*label+zs*zs),
      (k*ws*ws-xs*zs+label*label+2*label)**2+label*label*(xs+zs)**2]
    bounds=[abs(k)*H2+2*abs(label),abs(k*(label+2))*H2+2*H2,
      (label*label+H2)**2,(abs(k)*H2+H2+abs(label*label+2*label))**2+4*label*label*H2]
    for form,budget,degree in zip(forms,bounds,[2,2,4,4]):
     polynomial=S.Poly(S.expand(form),xx,zz,ww)
     assert polynomial.total_degree()<=degree
     checks['degree_bounds']+=1
     for coeff in polynomial.coeffs():
      assert abs(coeff)<=budget
      checks['collected_coefficients']+=1
   adj=C.adjugate()
   for ell in [2,3,5,7]:
    if M%ell==0:continue
    invdet=pow(determinant,-1,ell)
    ai=[[int(adj[i,j])*invdet%ell for j in range(3)] for i in range(3)]
    for yy in product(range(ell),repeat=3):
     cc=tuple(sum(ai[i][j]*yy[j] for j in range(3))%ell for i in range(3))
     out=tuple(sum(int(C[i,j])*cc[j] for j in range(3))%ell for i in range(3))
     assert out==yy
     checks['residue_inverse']+=1
    for label in [M,2*M,-2*M]:
     if label%ell==0:continue
     yy=(1,0,0) if (label+2)%ell==0 else (0,0,0)
     cc=tuple(sum(ai[i][j]*yy[j] for j in range(3))%ell for i in range(3))
     xx,zz,ww=map(int,C*S.Matrix(cc))
     K=(k*ww*ww+label*(label+2)-xx*zz)**2+label*label*(xx+zz)**2
     assert K%ell!=0
     checks['content_witness']+=1
   if checks['whole_lattice_bases']<=24:
    xx,zz,ww=S.symbols('x z w');syms=S.Matrix([xx,zz,ww]);xs,zs,ws=C*syms
    for label in [1,-2]:
     DD=(label*label+xs*xs)*(label*label+zs*zs)
     PP=k*ws*ws+2*label
     QQ=k*(label+2)*ws*ws-2*xs*zs
     assert S.Poly(S.gcd(S.Poly(PP,xx,zz,ww),S.Poly(DD,xx,zz,ww)),xx,zz,ww).total_degree()==0
     assert S.Poly(S.gcd(S.Poly(QQ,xx,zz,ww),S.Poly(DD,xx,zz,ww)),xx,zz,ww).total_degree()==0
     checks['same_basis_coprime']+=2
   Cbad=S.Matrix.hstack(S.Matrix(scale(2,u)),S.Matrix(v),S.Matrix(za))
   assert abs(Cbad.det())==2*M*M and (Cbad.inv()*S.Matrix(u))[0]==S.Rational(1,2)
   checks['nonprimitive_negative']+=1
for name in ['OriginalPolynomialExpansionBounds318','OriginalReducedPolynomialExpansions318','OriginalReducedCoefficientHeight318','OriginalReducedDegreeBounds318']:
 text=(Path(__file__).resolve().parent/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
U=S.Matrix(3,3,S.symbols('a:9'));assert all(S.expand(x)==0 for x in U*U.adjugate()-U.det()*S.eye(3));assert all(S.expand(x)==0 for x in U.adjugate()*U-U.det()*S.eye(3))
print('PASS',checks,'negative: independent proper sublattice fails integral spanning')
