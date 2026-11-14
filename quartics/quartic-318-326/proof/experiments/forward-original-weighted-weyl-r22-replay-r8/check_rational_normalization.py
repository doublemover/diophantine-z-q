#!/usr/bin/env python3
"""Exact rational-square normalization and actual rational cubic examples."""
import itertools,json,math
from fractions import Fraction as Q
from pathlib import Path
from sympy import factorint

def vp(p,x):
 x=Q(x);assert x;a,b=abs(x.numerator),x.denominator;e=0
 while a%p==0:a//=p;e+=1
 while b%p==0:b//=p;e-=1
 return e

def sqrtq(x):
 x=Q(x);assert x>0
 a,b=math.isqrt(x.numerator),math.isqrt(x.denominator)
 assert a*a==x.numerator and b*b==x.denominator
 return Q(a,b)

def mono(p,u):return math.prod(q for q,b in zip(p,u) if b)
def bit(a,q):return int(pow(a%q,(q-1)//2,q)!=1)
def mv(A,v):return [sum(x*y for x,y in zip(row,v))%2 for row in A]
checks=dict(supported_rational_classes=0,rational_curve_points=0,rational_square_multipliers=0,outside_valuation_checks=0,actual_finite_row_equations=0,actual_three_equations=0)
for primes in ((5,7,11),(7,19),(11,23,31),(5,11,17,23)):
 for u,eps,r in itertools.product(itertools.product((0,1),repeat=len(primes)),(0,1),[Q(a,b) for a in (-7,-2,1,5) for b in (1,3,4,11)]):
  x=(-1)**eps*mono(primes,u)*r*r
  uu=tuple(vp(p,x)%2 for p in primes)
  assert uu==u and int(x<0)==eps
  t=sqrtq(abs(x)/mono(primes,uu));assert x==(-1)**eps*mono(primes,uu)*t*t
  allp=set(factorint(abs(x.numerator)))|set(factorint(x.denominator))
  for q in allp-set(primes):assert vp(q,x)%2==0;checks['outside_valuation_checks']+=1
  checks['supported_rational_classes']+=1
seen=set()
for b in range(1,121):
 for a in range(-3*b+1,5*b):
  k=Q(a,b);C=k*(k-1)*(k+3)
  if C<=0 or k in seen:continue
  seen.add(k);f=factorint(C.numerator*C.denominator);n=math.prod(int(p) for p,e in f.items() if e%2)
  if n%12!=11:continue
  primes=sorted(map(int,factorint(n)));x=n*k;y=n*n*sqrtq(C/n);A=x+3*n;B=x-n
  assert x and A and B and y*y==x*B*A and A>0
  eps=int(B<0);delta=vp(3,A)%2
  u=tuple(vp(p,A)%2 for p in primes);v=tuple(vp(p,B)%2 for p in primes)
  r=sqrtq(A/(3**delta*mono(primes,u)));s=sqrtq(abs(B)/mono(primes,v))
  assert A==3**delta*mono(primes,u)*r*r and B==(-1)**eps*mono(primes,v)*s*s
  checks['rational_square_multipliers']+=2
  for Z,allowed in ((A,set(primes)|{3}),(B,set(primes))):
   allp=set(factorint(abs(Z.numerator)))|set(factorint(Z.denominator))
   for q in allp-allowed:assert vp(q,Z)%2==0;checks['outside_valuation_checks']+=1
  E=[[0 if i==j else bit(primes[j],primes[i]) for j in range(len(primes))] for i in range(len(primes))]
  K=[row[:] for row in E]
  for i in range(len(primes)):K[i][i]=sum(E[i])%2
  lam=[bit(3,p) for p in primes];par=[p//2%2 for p in primes]
  vv=tuple(t^eps for t in v);dd=delta^eps;Ku=mv(K,u);Kv=mv(K,vv)
  for i in range(len(primes)):
   assert (Ku[i]+lam[i]*vv[i]-dd*lam[i])%2==0
   assert (Kv[i]+par[i]*vv[i])%2==0
   checks['actual_finite_row_equations']+=2
  assert sum((a+b)*t for a,b,t in zip(lam,par,vv))%2==0
  checks['actual_three_equations']+=1;checks['rational_curve_points']+=1
result={'status':'PASS','checks':checks,'scope':'Actual arbitrary signed rational support normalization, nonzero rational square multipliers and exact rational cubic examples yielding the original finite descent equations. Examples are not asserted to realize the beta class on the produced simultaneous twists; global rational-point existence remains unproved.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
