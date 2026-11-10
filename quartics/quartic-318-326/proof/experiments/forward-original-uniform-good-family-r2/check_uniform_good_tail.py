from math import sqrt,floor,log,prod
from itertools import product
from fractions import Fraction
import sympy as s
checks=dict(scaled_widths=0,index_area=0,index_cylinders=0,height_radii=0,height_monotonicity=0,full_index_budgets=0,literal_family_weights=0)
def heights(k,t,L):
 H=(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t);K=2*L*L+t*t
 return 1+8*H*H*K*K+4*L**4+t*t*L*L
def full(k,t,A,B,C,Y,W):
 aa,bb=A+4*C,B+4*C;L=(aa+bb+10)*W;N=heights(k,t,L)
 return 512*A*B*C/Y*log(Y)+25*((2*aa+1)*(2*bb+1)*4*log(N)+8*((2*aa+1)+(2*bb+1))*(2*C+1)*log(Y))
assert 25*4*4802==480200 and 25*8*1764==352800 and 512*512==262144
for M in [1,3,5,7,15]:
 for a,b in product([0,1,M],[0,M]):
  u,v,w,z=(1,0,0),(0,M,0),(0,0,M),(a,b,M)
  assert sqrt(sum(x*x for x in z))<=2*M+1e-10
  assert abs(int(s.det(s.Matrix.hstack(*map(s.Matrix,[u,v,z])))))==M*M
  U,V,W=1,M,M
  for R in [M,2*M,3*M+1]:
   for T in [M,R]:
    A,B,C=floor(8*R/U),floor(8*R/V),floor(4*R/W)
    aa,bb=A+4*C,B+4*C
    alpha,beta,gamma=2*aa+1,2*bb+1,2*C+1
    assert alpha*U<=49*R and beta*V<=49*R and gamma*W<=9*R
    checks['scaled_widths']+=3
    assert alpha*beta*M*M<=4802*R*R*T;checks['index_area']+=1
    assert (alpha+beta)*gamma*M*M<=1764*R*R*T;checks['index_cylinders']+=1
    L=(aa+bb+10)*W
    assert L<=58*R*R;checks['height_radii']+=1
    for k,t,Y in product([-2,1,3],[-2,1,M,4*M],[3,5,11]):
     assert heights(k,t,L)<=heights(k,t,58*R*R)
     lhs=full(k,t,A,B,C,Y,W)*M*M
     rhs=262144*R**3/Y*log(Y)+480200*R*R*T*log(heights(k,t,58*R*R))+352800*R*R*T*log(Y)
     assert lhs<=rhs+1e-6
     checks['full_index_budgets']+=1
for k,t,L,H in product([-3,1,4],[-2,0,5],range(0,5),range(5,9)):
 assert heights(k,t,L)<=heights(k,t,H);checks['height_monotonicity']+=1
for k,t in product(range(1,6),range(1,101)):
 ps=[int(p) for p in s.factorint(t) if 2*k%p]
 M=prod(ps);count=prod(p+1 for p in ps)
 assert t%M==0
 weight=Fraction(count,M*M)
 assert weight==prod(Fraction(p+1,p*p) for p in ps)
 assert weight<=Fraction(2**len(ps),M)
 checks['literal_family_weights']+=1
print('PASS',checks,'original exact index; actual enlarged side/cylinder scaling; uniform height and retained radical weights')
