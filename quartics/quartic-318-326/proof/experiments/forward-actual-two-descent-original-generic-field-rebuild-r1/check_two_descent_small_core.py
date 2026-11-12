#!/usr/bin/env python3
"""Exact produced first-twist supports and actual deleted cores; no Lean run."""
import itertools,json,math
from pathlib import Path
from sympy import primerange
P=list(primerange(5,1000000))
count={'produced_families':0,'actual_core_entries':0,'coefficient_candidates':0,'coefficient_solutions':0}
def ch(a,p):
 v=pow(a%p,(p-1)//2,p);return -1 if v==p-1 else v
def bit(a,p):return int(ch(a,p)==-1)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%2
def mv(A,v):return [dot(r,v) for r in A]
def tp(A):return list(map(list,zip(*A)))
def rank(A):
 A=[r[:] for r in A];n=len(A);c=0
 for j in range(n):
  z=next((i for i in range(c,n) if A[i][j]),None)
  if z is None:continue
  A[c],A[z]=A[z],A[c]
  for i in range(n):
   if i!=c and A[i][j]:A[i]=[x^y for x,y in zip(A[i],A[c])]
  c+=1
 return c
for B in [[17],[17,73],[17,73,97],[17,73,97,193]]:
 assert math.prod(B)%24==17
 d=len(B)-1;C=[[int(b==i or b==d) for i in range(d)] for b in range(d+1)]
 for N in [0,100,1000,5000]:
  for forbidden in [set(),{7,13,19,31,43,61,79,103,109}]:
   aux=[]
   for i in range(d):
    targets=[C[b][i] for b in range(d+1)]+[0]*len(aux)
    q=next(q for q in P if q>max(N,2) and q%12==1 and q not in B+aux and q not in forbidden
           and all(bit(q,p)==b for p,b in zip(B+aux,targets)))
    aux.append(q)
   targets=[sum(r)%2 for r in C]+[0]*d
   q0=next(q for q in P if q>max(N,2) and q%12==7 and q not in B+aux and q not in forbidden
           and all(bit(q,p)==b for p,b in zip(B+aux,targets)))
   primes=B+aux+[q0];n=len(primes);l=math.prod(primes)
   assert len(set(primes))==n and l%12==11 and l>N
   s=[(p//2)%2 for p in primes];lam=[bit(3,p) for p in primes]
   beta=[int(i<len(B)) for i in range(n)];a=[int(i in [d,n-1]) for i in range(n)]
   K=[[0 if i==j else bit(primes[j],primes[i]) for j in range(n)] for i in range(n)]
   for i in range(n):K[i][i]=sum(K[i])%2
   assert mv(K,beta)==[0]*n and dot(a,beta)==1 and sum(a)%2==0
   assert sum(s[:len(B)])%2==0 and sum(lam[:len(B)])%2==1
   M=[[K[i][j]^(lam[i]*a[j]) for j in range(n)] for i in range(n)]
   core=[r[:-1] for r in M[:-1]];D=[r[:len(B)] for r in core[:len(B)]]
   assert sum(map(sum,D))%2==1 and rank(core)==n-1
   for i in range(n-1):
    for j in range(n-1):
     expected=D[i][j] if i<len(B) and j<len(B) else C[i][j-len(B)] if i<len(B) else C[j][i-len(B)] if j<len(B) else 0
     assert core[i][j]==expected
     count['actual_core_entries']+=1
   span={tuple(c^(e*b) for b in beta) for c,e in itertools.product([0,1],repeat=2)}
   for x in itertools.product([0,1],repeat=n):
    assert (mv(K,x)==[0]*n)==(x in span)
    assert mv(K,x)!=lam
   for v in itertools.product([0,1],repeat=n):
    count['coefficient_candidates']+=2**(n+1)
    if any(x^(z*y) for x,z,y in zip(mv(K,v),s,v)):continue
    if dot([x^y for x,y in zip(lam,s)],v):continue
    for u in itertools.product([0,1],repeat=n):
     for delta in [0,1]:
      if all(x^(z*y)==delta*z for x,z,y in zip(mv(K,u),lam,v)):
       assert delta==0 and not any(v) and u in span
       count['coefficient_solutions']+=1
   count['produced_families']+=1
result={'status':'PASS','checks':count,'scope':'Actual first-twist prime production through beta kernel, actual D/C/Ct/0 core, unit core, K kernel and all finite local coefficient equations. No enlarged theta-support or Selmer/Kummer point conclusion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
