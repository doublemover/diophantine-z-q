#!/usr/bin/env python3
"""Exact prime-symbol matrix and local-coefficient regressions; no Lean run."""
import itertools,json,math
from pathlib import Path
from sympy import primerange
P=list(primerange(5,1000000))
count={'prime_pairs':0,'actual_supports':0,'matrix_entries':0,'coefficient_candidates':0,'coefficient_solutions':0}
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
def actual(primes,nb,q0):
 n=len(primes);s=[(p//2)%2 for p in primes];lam=[bit(3,p) for p in primes]
 K=[[0 if i==j else bit(primes[j],primes[i]) for j in range(n)] for i in range(n)]
 for i in range(n):K[i][i]=sum(K[i])%2
 assert math.prod(primes)%12==11 and sum(s)%2==1 and sum(lam)%2==0
 assert mv(K,[1]*n)==mv(tp(K),[1]*n)==[0]*n
 for i in range(n):
  for j in range(n):
   assert K[i][j]^K[j][i]==(s[i]*s[j])^(s[i] if i==j else 0)
   count['matrix_entries']+=1
 beta=[int(i<nb) for i in range(n)];a=[int(i in [0,q0]) for i in range(n)]
 if mv(K,beta)!=[0]*n:return None
 M=[[K[i][j]^(lam[i]*a[j]) for j in range(n)] for i in range(n)]
 keep=[i for i in range(n) if i!=q0];core=[[M[i][j] for j in keep] for i in keep]
 if rank(core)!=n-1:return None
 assert mv(M,[1]*n)==mv(tp(M),[1]*n)==[0]*n
 assert mv(M,beta)==lam
 for v in itertools.product([0,1],repeat=n):
  assert mv(M,[x^(dot(a,v)*b) for x,b in zip(v,beta)])==mv(K,v)
  assert mv(K,v)!=lam
  for u in itertools.product([0,1],repeat=n):
   for delta in [0,1]:
    count['coefficient_candidates']+=1
    first=all(x^(l*y)==delta*l for x,l,y in zip(mv(K,u),lam,v))
    second=all(x^(z*y)==0 for x,z,y in zip(mv(K,v),s,v))
    third=dot([x^y for x,y in zip(lam,s)],v)==0
    if first and second and third:
     assert delta==0 and not any(v)
     assert any(list(u)==[c^(d*b) for b in beta] for c,d in itertools.product([0,1],repeat=2))
     count['coefficient_solutions']+=1
 count['actual_supports']+=1
 return K
for p,q in itertools.combinations(list(primerange(5,120)),2):
 assert (bit(p,q)^bit(q,p))==((p//2)%2)*((q//2)%2)
 count['prime_pairs']+=1
for B in [[17],[17,73],[17,97],[17,73,97]]:
 for theta in [None]+[p for p in P if p%24==1 and p not in B and all(ch(p,b)==1 for b in B)][:1]:
  for N in [20,100]:
   seed=B+([] if theta is None else [theta]);qs=[];d=len(B)-1
   for i in range(d):
    targets=[int(j==i or j==len(B)-1) for j in range(len(B))]+([0] if theta else [])+[0]*i
    q=next(q for q in P if q>N and q%12==1 and q not in seed+qs and all(bit(q,p)==b for p,b in zip(seed+qs,targets)))
    qs.append(q)
   for toggle in ([0,1] if theta else [0]):
    targets=[1]*d+[d%2]+([toggle] if theta else [])+[0]*d
    q0=next(q for q in P if q>N and q%12==7 and q not in seed+qs and all(bit(q,p)==b for p,b in zip(seed+qs,targets)))
    small=B+qs+[q0]
    assert actual(small,len(B),len(small)-1) is not None
    if theta is None or actual(small+[theta],len(B),len(small)-1) is not None:break
   else:raise AssertionError('No diagonal choice')
result={'status':'PASS','checks':count,'scope':'Actual Legendre K, reciprocity, product parity, K-sharp completion/projection and all local coefficient equations. No Selmer/Kummer or rational-point existence assertion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
