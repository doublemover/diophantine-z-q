#!/usr/bin/env python3
"""Independent finite-precision checks of the exact Hensel constructions."""
import json,math
from pathlib import Path
from sympy import sqrt_mod,jacobi_symbol
source=Path(__file__).with_name('check_two_descent_mutual_support.py').read_text();supports=[]
exec(source[:source.index('def check_support')]+"def check_support(primes,nb,N): supports.append((primes,nb,N,tuple(B),tuple(J)))\n"+source[source.index('for B in'):source.index('result=')])
checks=dict(actual_twists=len(supports),odd_hensel_steps=0,two_hensel_steps=0,mutual_roots=0,two_adic_roots=0,three_torsion_roots=0)
def odd_root(A,p):
 assert p!=2 and math.gcd(A,p)==1 and int(jacobi_symbol(A,p))==1
 r=int(sqrt_mod(A,p));assert r%p and (r*r-A)%p==0;m=p
 for k in range(1,9):
  t=((A-r*r)//m*pow(2*r,-1,p))%p;r+=t*m;m*=p
  assert (r*r-A)%m==0 and r%p;checks['odd_hensel_steps']+=1
 return r,m
def two_root(A):
 assert A%8==1;r=1;m=8
 for k in range(3,17):
  t=((A-r*r)//m)%2;r+=t*(m//2);m*=2
  assert (r*r-A)%m==0 and r%2;checks['two_hensel_steps']+=1
 return r,m
for primes,nb,N,B,J in supports:
 beta=math.prod(B);theta=math.prod(J);n=math.prod(primes)
 assert beta%24==17 and theta%24==1 and n%12==11
 for A in [beta,theta]:
  r,m=two_root(A);assert r*r%m==A%m;checks['two_adic_roots']+=1
 for q in B:
  r,m=odd_root(theta,q);assert r*r%m==theta%m;checks['mutual_roots']+=1
 for q in J:
  r,m=odd_root(beta,q);assert r*r%m==beta%m;checks['mutual_roots']+=1
 s,m=odd_root(beta*n,3);r=s*pow(n,-1,m)%m
 assert r%3 and (n*r*r-beta)%m==0;checks['three_torsion_roots']+=1
result={'status':'PASS','checks':checks,'scope':'Actual finite-precision Hensel/Newton roots for mutual products,2-adic17/1mod24 units,and beta versus both actual twist parameters at3. These regressions are not the Lean proof or actual curve-point existence.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
