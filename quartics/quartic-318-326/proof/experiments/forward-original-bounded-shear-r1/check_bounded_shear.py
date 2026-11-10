from itertools import product
from pathlib import Path
import sympy as S
checks={'field_quadratics':0,'integer_fibers':0,'large_integer_fibers':0,'grid_leading_choices':0,'exceptional_grid_choices':0,'determinant_shears':0,'same_point_inverse':0,'anisotropic_inverse':0}
def det(u,v,z):return u[0]*(v[1]*z[2]-v[2]*z[1])-v[0]*(u[1]*z[2]-u[2]*z[1])+z[0]*(u[1]*v[2]-u[2]*v[1])
A,B,C,D,E,F,a,b,c=S.symbols('A B C D E F a b c')
q=lambda x,y,z:A*x*x+B*y*y+C*z*z+D*x*y+E*x*z+F*y*z
rhs=(a*a+a*c-2*a*b)*q(1,0,1)+(a*a-a*c)*q(-1,0,1)+(b*b+b*c-2*a*b)*q(0,1,1)+(b*b-b*c)*q(0,-1,1)+2*a*b*q(1,1,1)+(2*c*c-2*a*a-2*b*b+2*a*b)*q(0,0,1)
assert S.expand(2*q(a,b,c)-rhs)==0
for p in [2,3,5,7]:
 for aa,bb,cc in product(range(1,p),range(p),range(p)):
  roots=[x for x in range(p) if (aa*x*x+bb*x+cc)%p==0]
  assert len(roots)<=2;checks['field_quadratics']+=1
  for B0 in range(7):
   integer=[x for x in range(-B0,B0+1) if (aa*x*x+bb*x+cc)%p==0]
   assert len(integer)<=2*(2*B0//p+1);checks['integer_fibers']+=1
   if p>2*B0:
    assert len(integer)<=2;checks['large_integer_fibers']+=1
matrices=[]
for entries in product([0,1],repeat=9):
 u,v,z=entries[:3],entries[3:6],entries[6:]
 if det(u,v,z):matrices.append((u,v,z))
for p in [5,7,11]:
 for u,v,z in matrices:
  if det(u,v,z)%p==0:continue
  for k in [1,2]:
   for t in range(p):
    good=[]
    for i,j in product(range(5),repeat=2):
     x,zz,w=[z[l]+i*u[l]+j*v[l] for l in range(3)]
     if (k*w*w)%p and (k*(t+2)*w*w-2*x*zz)%p:good.append((i,j))
    assert len(good)>=5 # Schwartz-Zippel degree4 on25 points.
    checks['grid_leading_choices']+=1
    if (t+2)%p==0:checks['exceptional_grid_choices']+=1
for u,v,z in matrices[:30]:
 for i,j in product(range(5),repeat=2):
  dz=tuple(z[l]+i*u[l]+j*v[l] for l in range(3))
  assert det(u,v,dz)==det(u,v,z);checks['determinant_shears']+=1
  for a,b,c in product([-2,0,2],repeat=3):
   old=tuple(a*u[l]+b*v[l]+c*z[l] for l in range(3))
   new=tuple((a-i*c)*u[l]+(b-j*c)*v[l]+c*dz[l] for l in range(3))
   assert old==new;checks['same_point_inverse']+=1
   assert abs(a-i*c)<=2+4*2 and abs(b-j*c)<=2+4*2;checks['anisotropic_inverse']+=1
# Half width alone is not the injective-residue criterion.
assert len([h for h in range(-3,4) if ((h-2)*(h-3))%5==0])==4
# A bad individual pivot is NOT reason to omit a prime: standard z=(0,0,1),t=-2.
u,v,z=(1,0,0),(0,1,0),(0,0,1)
assert (-2*z[0]*z[1])%5==0
assert (-2*(z[0]+u[0]+v[0])*(z[1]+u[1]+v[1]))%5!=0
for name in ['OriginalQuadraticIntegerFibers318','OriginalAffineLeadingForms318','OriginalFiveGridLeading318','OriginalBoundedIntegerShear318']:
 text=(Path(__file__).parent/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'homogeneous six-point identity; bad-pivot negative control retained')
