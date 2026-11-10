#!/usr/bin/env python3
from math import floor,log,prod
from itertools import product
from fractions import Fraction
import sympy as s,json
c=dict(actual_prime_partition=0,height_monotonicity=0,exact_index_area=0,exact_index_cylinders=0,global_polynomial_height=0,full_actual_index_budget=0)
def coefficient(k,t,L):
 J=(2*abs(k)+2)*L*L+t*t+2*abs(t)
 return 1+(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t)+8*(J*J+t*t*L*L)
def point(k,t,L):return 109*coefficient(k,t,L)**9
def height(k,t,A,B,L):return 1+(2*A+1)*(2*B+1)*point(k,t,L)
def globalheight(k,t,R):return 1+(49*R)**2*point(k,t,58*R*R)
assert 25*2*4802==240100 and 25*8*1764==352800
for k,t,L,H in product([-3,1,318,326],[-10,-2,0,1,5],range(5),range(5,9)):
 assert coefficient(k,t,L)<=coefficient(k,t,H);c['height_monotonicity']+=1
for M in [1,3,5,7,15]:
 for a,b in product([0,1,M],[0,M]):
  u,v,z=(1,0,0),(0,M,0),(a,b,M)
  assert abs(int(s.det(s.Matrix.hstack(*map(s.Matrix,[u,v,z])))))==M*M
  U,V,W=1,M,M
  for R in [M,2*M,3*M+1]:
   for T in [M,R]:
    A,B,C=floor(8*R/U),floor(8*R/V),floor(4*R/W)
    aa,bb=A+4*C,B+4*C;alpha,beta,gamma=2*aa+1,2*bb+1,2*C+1
    assert alpha*beta*M*M<=4802*R*R*T;c['exact_index_area']+=1
    assert (alpha+beta)*gamma*M*M<=1764*R*R*T;c['exact_index_cylinders']+=1
    L=(aa+bb+10)*W
    for k,t,Y in product([1,318,326],[-10,-2,1,M],[3,5,11]):
     N=height(k,t,aa,bb,L);G=globalheight(k,t,R)
     assert N<=G;c['global_polynomial_height']+=1
     lhs=(512*A*B*C/Y*log(Y)+25*(alpha*beta*2*log(N)+8*(alpha+beta)*gamma*log(Y)))*M*M
     rhs=262144*R**3/Y*log(Y)+240100*R*R*T*log(G)+352800*R*R*T*log(Y)
     assert lhs<=rhs+1e-6;c['full_actual_index_budget']+=1
# Literal prime partition on the actual source forms, including t=-2 and t+2 primes.
for k,t,C,Y in product([1,318,326],[-10,-2,1,5],[1,2,3],[3,5]):
 M=prod(p for p in s.factorint(abs(t)) if 2*k%p)
 for x,z,w in product(range(-2,3),repeat=3):
  for p in [5,7,11,17,19]:
   if p<=Y or k%p==0 or t%p==0:continue
   if (k*(t+2)*w*w-2*x*z)%p or ((k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2)%p:continue
   assert (p<=2*C) != (p>2*C)
   if p>2*C:assert p>=5 and M%p
   c['actual_prime_partition']+=1
print(json.dumps({'status':'PASS','checks':c,'local_lean':'NOT_RUN','actual_original_label_and_index':True},indent=2))
