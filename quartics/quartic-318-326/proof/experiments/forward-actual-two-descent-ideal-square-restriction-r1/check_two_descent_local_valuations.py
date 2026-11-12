#!/usr/bin/env python3
"""Exact valuation alternatives and finite-precision actual local torsion tests."""
import itertools,json,math
from pathlib import Path
from fractions import Fraction as Q
from sympy import primerange,sqrt_mod
source=Path(__file__).with_name('check_two_descent_mutual_support.py').read_text();supports=[]
exec(source[:source.index('def check_support')]+"def check_support(primes,nb,N): supports.append((primes,nb,N))\n"+source[source.index('for B in'):source.index('result=')])
checks=dict(integer_triples=0,good_local_points=0,bad_local_points=0,torsion_classes=[0,0,0,0],hensel_steps=0,square_witnesses=0)
def pair(a,b):return (a==b and a<=0) or (a==0 and b>=0) or (a>=0 and b==0)
for a,b,c in itertools.product(range(-8,9),repeat=3):
 if pair(a,b) and pair(a,c) and pair(b,c) and (a+b+c)%2==0:
  assert a%2==b%2==c%2==0;checks['integer_triples']+=1
def vp(p,x):
 x=Q(x);assert x
 a,b=abs(x.numerator),x.denominator;e=0
 while a%p==0:a//=p;e+=1
 while b%p==0:b//=p;e-=1
 return e
def unit(p,x):return x/(Q(p)**vp(p,x))
def issq(p,x):
 if not x:return True
 e=vp(p,x)
 if e%2:return False
 u=unit(p,x);a=u.numerator*pow(u.denominator,-1,p)%p
 return pow(a,(p-1)//2,p)==1
def lift_square(p,x):
 assert x and issq(p,x);e=vp(p,x);u=unit(p,x);a=u.numerator*pow(u.denominator,-1,p)%p;r=int(sqrt_mod(a,p));m=p
 for _ in range(6):
  nextmod=m*p;A=u.numerator*pow(u.denominator,-1,nextmod)%nextmod
  t=((A-r*r)//m*pow(2*r,-1,p))%p;r+=t*m;m=nextmod
  assert (r*r*u.denominator-u.numerator)%m==0;checks['hensel_steps']+=1
 checks['square_witnesses']+=1
 return Q(r)*Q(p)**(e//2)
for n in [1,7,11,19,35,143]:
 for p in list(primerange(5,32)):
  if n%p==0:continue
  for den in [1,p*p]:
   for num in range(-35,36):
    x=Q(num,den);A=x+3*n;B=x-n;f=x*A*B
    if not f or not issq(p,f):continue
    assert vp(p,x)%2==vp(p,A)%2==vp(p,B)%2==0
    checks['good_local_points']+=1
for primes,nb,N in supports:
 n=math.prod(primes)
 for p in primes:
  assert vp(p,Q(n))==1
  cases=[(Q(1),0),(Q(1,p*p),0),(Q(n+p*p),1),(Q(-3*n+3*p*p),2),(Q(-3*p*p),3)]
  for x,t in cases:
   A=x+3*n;B=x-n;f=x*A*B;assert f and issq(p,f)
   vx,va,vb=vp(p,x),vp(p,A),vp(p,B)
   chosen=0 if vx<1 else 3 if vx>1 else 1 if vb>1 else 2 if va>1 else None
   assert chosen==t
   c,d=[(Q(1),Q(1)),(Q(n),Q(1)),(Q(3),Q(-n)),(Q(3*n),Q(-n))][t]
   assert issq(p,A/c) and issq(p,B/d)
   lift_square(p,A/c);lift_square(p,B/d);lift_square(p,f)
   checks['bad_local_points']+=1;checks['torsion_classes'][t]+=1
result={'status':'PASS','checks':checks,'scope':'Actual Q_p valuation alternatives and squareclass identities for original cubic: odd-good necessary even valuations, all four odd-support torsion classes with finite-precision witnesses on both produced supports. Not hosted Lean, complete Selmer interpretation, or global rational-point existence.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
