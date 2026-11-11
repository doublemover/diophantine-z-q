#!/usr/bin/env python3
"""Finite-precision actual curve/Kummer coordinates at every treated place."""
import json,math
from pathlib import Path
from fractions import Fraction as Q
from sympy import sqrt_mod
source=Path(__file__).with_name('check_two_descent_mutual_support.py').read_text();supports=[]
exec(source[:source.index('def check_support')]+"def check_support(primes,nb,N): supports.append((primes,nb,N,tuple(B),tuple(J)))\n"+source[source.index('for B in'):source.index('result=')])
checks=dict(actual_twists=len(supports),two_adic_points=0,three_adic_points=0,support_prime_points=0,curve_residuals=0,kummer_residuals=0,real_constructions=0,lifting_steps=0)
def vp(p,x):
 x=Q(x)
 if not x:return 10**9
 a,b=abs(x.numerator),x.denominator;e=0
 while a%p==0:a//=p;e+=1
 while b%p==0:b//=p;e-=1
 return e
def root(p,A,K):
 A=Q(A);e=vp(p,A);assert A and e%2==0
 u=A/Q(p)**e
 if p==2:
  assert (u.numerator*pow(u.denominator,-1,8))%8==1;r=1;m=8
  for k in range(3,K):
   mm=2*m;a=u.numerator*pow(u.denominator,-1,mm)%mm;t=((a-r*r)//m)%2;r+=t*(m//2);m=mm;checks['lifting_steps']+=1
 else:
  a=u.numerator*pow(u.denominator,-1,p)%p;r=int(sqrt_mod(a,p));m=p
  assert r
  for k in range(1,K):
   mm=p*m;a=u.numerator*pow(u.denominator,-1,mm)%mm;t=((a-r*r)//m*pow(2*r,-1,p))%p;r+=t*m;m=mm;checks['lifting_steps']+=1
 z=Q(r)*Q(p)**(e//2);assert z and vp(p,z*z-A)>=K+e;return z

def check_point(p,n,beta,first):
 k=max(0,vp(p,Q(n)))+3;K=40+8*k;b=Q(p)**k
 if first:
  x=Q(n)+b*b;A=x+3*n;B=x-n
  r=root(p,x/n,K);s=root(p,A/(4*n),K);y=2*n*b*r*s;u0=2*s;v=b;c=Q(n)
 else:
  x=1/(b*b);A=x+3*n;B=x-n
  r=root(p,A/x,K);s=root(p,B/x,K);y=r*s/(b**3);u0=r/b;v=s/b;c=Q(1)
 t=root(p,Q(beta)/c,K);u=u0/t
 assert x and u and v and A and B
 assert vp(p,y*y-x*B*A)>=20
 assert vp(p,A-beta*u*u)>=20 and vp(p,B-v*v)>=20
 checks['curve_residuals']+=1;checks['kummer_residuals']+=2
for primes,nb,N,B,J in supports:
 n=math.prod(primes);beta=math.prod(B)
 check_point(2,n,beta,False);checks['two_adic_points']+=1
 check_point(3,n,beta,True);checks['three_adic_points']+=1
 for p in primes:
  check_point(p,n,beta,beta%p==0);checks['support_prime_points']+=1
 x=Q(n+1);A=x+3*n;B=x-n;assert beta>0 and x>0 and A>0 and B==1 and x*B*A==(n+1)*(4*n+1)
 checks['real_constructions']+=1
result={'status':'PASS','checks':checks,'scope':'Constructed finite-precision nonzero local curve points and both literal Kummer equations for original beta on BOTH actual twists at2,3,every support prime and infinity. Does not prove good-prime sufficiency or global rational points.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
