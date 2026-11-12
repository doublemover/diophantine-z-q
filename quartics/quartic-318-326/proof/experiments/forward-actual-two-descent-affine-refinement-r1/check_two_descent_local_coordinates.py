#!/usr/bin/env python3
"""Actual representatives, valuations, Jacobi units and torsion signatures."""
import itertools,json,math
from pathlib import Path
from fractions import Fraction
from sympy import jacobi_symbol
source=Path(__file__).with_name('check_two_descent_mutual_support.py').read_text()
supports=[]
exec(source[:source.index('def check_support')]+"def check_support(primes,nb,N): supports.append((primes,nb,N))\n"+source[source.index('for B in'):source.index('result=')])
checks=dict(actual_supports=len(supports),representative_valuations=0,stripped_symbols=0,three_symbols=0,torsion_comparisons=0,normalizations=0,positive_classes=0,signed_classes=0,distinct_squareclasses=0)
def monomial(p,v):return math.prod(q**e for q,e in zip(p,v))
def vp(q,n):
 e=0
 while n%q==0:e+=1;n//=q
 return e
def square(q):return q>=0 and math.isqrt(q.numerator)**2==q.numerator and math.isqrt(q.denominator)**2==q.denominator
for p,nb,N in supports:
 n=len(p);K,M,lam,s=mats(p,nb);E=[[0 if i==j else bit(p[j],p[i]) for j in range(n)] for i in range(n)];rows=[sum(r)%2 for r in E];beta=tuple(int(i<nb) for i in range(n));vectors=list(itertools.product([0,1],repeat=n));positive=[]
 for u in vectors:
  A=monomial(p,u);Eu=mv(E,u)
  for i,q in enumerate(p):
   assert vp(q,A)==u[i]
   stripped=A//q**u[i]
   assert math.gcd(stripped,q)==1 and int(jacobi_symbol(stripped,q))==(-1)**Eu[i]
   checks['representative_valuations']+=1;checks['stripped_symbols']+=1
   for delta in [0,1]:
    assert vp(q,3**delta*A)==u[i]
    assert int(jacobi_symbol(3**delta*stripped,q))==(-1)**(delta*lam[i]^Eu[i])
    checks['representative_valuations']+=1;checks['stripped_symbols']+=1
  assert int(jacobi_symbol(A,3))==(-1)**dot([a^b for a,b in zip(lam,s)],u)
  checks['three_symbols']+=1
  for eps,delta in itertools.product([0,1],repeat=2):
   v=tuple(reversed(u));Ev=mv(E,v);t=tuple(x^eps for x in v);Et=mv(E,t)
   for i in range(n):
    signed=(u[i],delta*lam[i]^Eu[i],v[i],eps*s[i]^Ev[i]);T2=(0,lam[i],1,s[i]^rows[i]);normalized=(u[i],(delta^eps)*lam[i]^Eu[i],t[i],Et[i])
    assert normalized==tuple(x^(eps*y) for x,y in zip(signed,T2));checks['normalizations']+=1
 for v in vectors:
  Ev=mv(E,v);Kv=mv(K,v);second=all(Ev[i]==v[i]*(s[i]^rows[i]) for i in range(n))
  assert second==all(Kv[i]==s[i]*v[i] for i in range(n))
  if not second or int(jacobi_symbol(monomial(p,v),3))!=1:continue
  for u in vectors:
   Eu=mv(E,u);Ku=mv(K,u)
   for delta in [0,1]:
    local=all(delta*lam[i]^Eu[i]==u[i]*rows[i]^v[i]*lam[i] for i in range(n))
    matrix=all(Ku[i]^lam[i]*v[i]==delta*lam[i] for i in range(n))
    assert local==matrix;checks['torsion_comparisons']+=n
    if local:positive.append((delta,u,v))
 assert len(positive)==4 and all(delta==0 and not any(v) for delta,u,v in positive)
 assert {u for delta,u,v in positive}=={tuple(c^(e*b) for b in beta) for c,e in itertools.product([0,1],repeat=2)}
 signed=[(eps,delta^eps,u,tuple(x^eps for x in v)) for eps in [0,1] for delta,u,v in positive]
 assert len(set(signed))==8
 representatives=[(Fraction(3**delta*monomial(p,u)),Fraction((-1)**eps*monomial(p,v))) for eps,delta,u,v in signed]
 for (A,B),(C,D) in itertools.combinations(representatives,2):
  assert not (square(A/C) and square(B/D));checks['distinct_squareclasses']+=1
 checks['positive_classes']+=len(positive);checks['signed_classes']+=len(signed)
result={'status':'PASS','checks':checks,'scope':'Literal integer representatives, rational squareclass separation, valuation/Jacobi signatures and support-prime torsion comparisons; four positive/eight signed comparison classes on both actual supports. No elliptic local-image or Selmer equality and no rational curve-point existence.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
