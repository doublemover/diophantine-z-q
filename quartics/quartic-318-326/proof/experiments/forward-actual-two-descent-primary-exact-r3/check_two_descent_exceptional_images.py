#!/usr/bin/env python3
"""Exact rational local-square tests of necessary exceptional image restrictions."""
import json,itertools,math
from pathlib import Path
from fractions import Fraction as Q

def vp(p,x):
 x=Q(x);assert x
 a,b=abs(x.numerator),x.denominator;e=0
 while a%p==0:a//=p;e+=1
 while b%p==0:b//=p;e-=1
 return e

def square(p,x):
 if not x:return True
 e=vp(p,x)
 if e%2:return False
 u=x/Q(p)**e;m=8 if p==2 else p
 z=u.numerator*pow(u.denominator,-1,m)%m
 return z==1 if p==2 else pow(z,(p-1)//2,p)==1

checks=dict(mod8_unit_obstructions=0,two_adic_curve_candidates=0,two_adic_points=0,
 three_adic_curve_candidates=0,three_adic_points=0,real_points=0,same_support_twists=0)
for n,U,W in itertools.product((3,7),(1,3,5,7),(1,3,5,7)):
 assert (W*W-(n+2*U)*U*(U+2*n))%8!=0
 checks['mod8_unit_obstructions']+=1
for n in range(3,100,4):
 for e in range(-6,7):
  for u in range(1,64,2):
   for sign in (-1,1):
    x=sign*Q(2)**e*u;A=x+3*n;B=x-n
    if not A or not B:continue
    checks['two_adic_curve_candidates']+=1
    if square(2,x*A*B):
     assert vp(2,A)%2==0 and vp(2,B)%2==0
     checks['two_adic_points']+=1
for n in range(2,100,3):
 for e in range(-5,6):
  for u in range(1,82):
   if u%3==0:continue
   for sign in (-1,1):
    x=sign*Q(3)**e*u;A=x+3*n;B=x-n
    if not A or not B:continue
    checks['three_adic_curve_candidates']+=1
    if square(3,x*A*B):
     assert square(3,B)
     checks['three_adic_points']+=1
for n in range(1,40):
 for k in range(-13*n,5*n):
  x=Q(k,4);A=x+3*n;B=x-n
  if x and A and B and x*A*B>0:
   assert A>0
   assert (n<x and B>0) or (-3*n<x<0 and B<0)
   checks['real_points']+=1
source=Path(__file__).with_name('check_two_descent_mutual_support.py').read_text();supports=[]
exec(source[:source.index('def check_support')]+"def check_support(primes,nb,N): supports.append(primes)\n"+source[source.index('for B in'):source.index('result=')])
for primes in supports:
 n=math.prod(primes);assert n%12==11 and n%4==3 and n%3==2
 checks['same_support_twists']+=1
result={'status':'PASS','checks':checks,'scope':'Necessary original-coordinate restrictions for actual exceptional local images, corroborated by exact rational p-adic square criteria and all32 mod8 unit cases. No global rational-point or Selmer-identification claim.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
