#!/usr/bin/env python3
from itertools import product
from collections import defaultdict
import sympy as s
for p in [2,3,5,7]:
 m=p*p;left=defaultdict(list);right=defaultdict(list)
 for a,c in product(range(m),repeat=2):left[(a*a+a*c-c*c)%m].append((a,c))
 for b,d in product(range(m),repeat=2):right[(210*b*b+210*b*d+42*d*d)%m].append((b,d))
 count=0
 for r,ac in left.items():
  for a,c in ac:
   for b,d in right.get((-r)%m,[]):
    assert all(x%p==0 for x in[a,b,c,d]);count+=1
 assert count==p**4
 print(f'PASS exhaustive norm-zero mod{m}: all {m**4} coordinate tuples covered by exact pair-sum partition; {count} zeros, all divisible by{p}.')
r,i,j,k,q=s.symbols('r i j k q');a=[r-j,i-5*k,2*j,10*k]
def poly(a):A,B,C,D=a;return A*A+A*C+210*B*B+210*B*D-C*C+42*D*D
N=r*r+210*i*i-5*j*j-1050*k*k
assert s.expand(poly(a)-N)==0
assert s.expand(poly([q*x for x in a])-q*q*poly(a))==0
def mul(x,y):
 r,i,j,k=x;R,I,J,K=y
 return(r*R-210*i*I+5*j*J+1050*k*K,r*I+i*R-5*j*K+5*k*J,r*J+j*R-210*i*K+210*k*I,r*K+k*R+i*J-j*I)
assert all(s.expand(x-y)==0 for x,y in zip(mul([r,i,j,k],[r,-i,-j,-k]),[N,0,0,0]))
assert all(s.expand(x-y)==0 for x,y in zip(mul([r,-i,-j,-k],[r,i,j,k]),[N,0,0,0]))
print('PASS exact original coordinate inverse, homogeneous norm scaling and both conjugate-norm identities. P-adic completeness/normalization applications require hosted Lean verification.')
