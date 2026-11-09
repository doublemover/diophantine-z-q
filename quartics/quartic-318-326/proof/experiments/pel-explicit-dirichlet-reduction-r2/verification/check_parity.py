#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from fractions import Fraction
import runpy
P=Path(__file__).resolve().parents[1]
a=runpy.run_path(str(P/'verification/check_inertia_relations.py'))
mul,norm,bar,s=a['mul'],a['norm'],a['bar'],a['s'];one=a['one'];N=a['N']
x=s.Matrix(s.symbols('x:4'));y=s.Matrix(s.symbols('y:4'))
assert s.expand(norm(mul(x,y))-norm(x)*norm(y))==0
primes=[2,3,5,7]
def val(p,x):
 x=Fraction(x);assert x
 n=0;a,b=abs(x.numerator),x.denominator
 while a%p==0:a//=p;n+=1
 while b%p==0:b//=p;n-=1
 return n
def parity(x):return tuple(val(p,norm(x))%2 for p in primes)
seen={}
for bits in product([0,1],repeat=4):
 w=one
 for bit,n in zip(bits,N):
  if bit:w=mul(w,n)
 assert norm(w)>0 and parity(w)==bits
 seen[bits]=w
assert len(seen)==16
for b,w in seen.items():
 for c,z in seen.items():assert parity(mul(w,z))==tuple((i+j)%2 for i,j in zip(b,c))
for q in [Fraction(-5,14),Fraction(1,210),Fraction(210),Fraction(7,8),Fraction(-1)]:
 assert parity(q*one)==(0,0,0,0)
for e,l in zip(a['a']['A'],a['a']['labels']):assert parity(e)==tuple(l)
print('PASS: actual reduced norm polynomial multiplicativity,16 positive original prime words, all256 parity products, negative rational valuations/scalars, exact original five inertia classes. Kernel=scalar-times-units NOT inferred.')
