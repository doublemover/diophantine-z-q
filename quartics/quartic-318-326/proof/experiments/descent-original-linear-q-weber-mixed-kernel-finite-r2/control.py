#!/usr/bin/env python3
"""Exact mixed coordinate control in finite fields and local quotient rings."""
from itertools import product
import json

def formula(t,w,A,B,m):
 inv=lambda a:pow(a%m,-1,m)
 u=inv(1+t*w)
 beta=inv(1-A*t*t*u)
 D=(t-A*w)%m
 H=(2*B+(3*A*A-1)*t-(A**3+A)*w)%m
 assert (w-t**3*u)%m==0 and (D*beta-t)%m==0
 assert (w*(1+B*w)**2-(t+2*A*w)*D**2-w*w*H)%m==0
 X=(A+t*u*beta*beta*H)%m
 Y=(-B+(1+B*w)*u*beta**3*H)%m
 return D,u,beta,X,Y

def finite(p):
 inv=lambda a:pow(a%p,-1,p)
 points=[(x,y) for x,y in product(range(p),repeat=2) if (y*y-x**3+x)%p==0]
 considered=0; two_torsion=0
 for (x,y),(A,B) in product(points,repeat=2):
  if not x or not y or x==A:continue
  t,w=-x*inv(y)%p,-inv(y)%p
  D,u,beta,X,Y=formula(t,w,A,B,p)
  slope=(y-B)*inv(x-A)%p
  assert slope==(-(1+B*w)*inv(D))%p
  exp_x=(slope*slope-x-A)%p
  exp_y=(-(slope*(exp_x-x)+y))%p
  assert (X,Y)==(exp_x,exp_y)
  considered+=1; two_torsion+=not B
 return considered,two_torsion

def local(p,e):
 m=p**e
 sqrt={}
 for b in range(m):sqrt.setdefault((b*b)%m,b)
 points=[(a,sqrt[(a**3-a)%m]) for a in range(m) if (a**3-a)%m in sqrt][:61]
 total=0
 for t,(A,B) in product(range(0,min(m,21*p),p),points):
  w=0
  for _ in range(e+1):w=(t**3-t*w*w)%m
  assert (w+t*w*w-t**3)%m==0
  D,u,beta,X,Y=formula(t,w,A,B,m)
  assert u%p==beta%p==1
  assert (X%p,Y%p)==(A%p,B%p)
  total+=1
 return total

F=[finite(p) for p in (5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61)]
R=[local(p,e) for p,e in ((3,5),(5,5),(7,4),(11,4))]
print(json.dumps(dict(field_pairs=sum(a for a,b in F),field_Q_two_torsion=sum(b for a,b in F),
 local_ring_pairs=sum(R), local_by_prime=R),sort_keys=True))
