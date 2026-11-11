#!/usr/bin/env python3
"""Actual q0 replacement realizes simultaneous diagonal choice; no Lean run."""
import itertools,json,math
from pathlib import Path
from sympy import primerange
P=list(primerange(5,1000000));counts={'actual_replacements':0,'fixed_prime_values':0,'full_core_entries':0,'old_core_entries':0,'kernel_vectors':0}
def bit(a,p):return int(pow(a%p,(p-1)//2,p)==p-1)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%2
def mv(A,v):return [dot(r,v) for r in A]
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
def matrices(primes,nb):
 n=len(primes);lam=[bit(3,p) for p in primes];a=[int(i in [nb-1,n-1]) for i in range(n)]
 K=[[0 if i==j else bit(primes[j],primes[i]) for j in range(n)] for i in range(n)]
 for i in range(n):K[i][i]=sum(K[i])%2
 M=[[K[i][j]^(lam[i]*a[j]) for j in range(n)] for i in range(n)]
 return K,M,lam
for B in [[17],[17,73],[17,73,97]]:
 theta_candidates=[q for q in P if q%24==1 and q not in B and all(bit(q,b)==0 for b in B)][:2]
 for nj in range(3):
  J=theta_candidates[:nj];seed=B+J;d=len(B)-1;C=[[int(b==i or b==d) for i in range(d)] for b in range(d+1)]
  for N in [20,1000]:
   I=[]
   for i in range(d):
    targets=[C[b][i] for b in range(len(B))]+[0]*len(J)+[0]*len(I)
    r=next(r for r in P if r>N and r%12==1 and r not in seed+I and all(bit(r,p)==b for p,b in zip(seed+I,targets)))
    I.append(r)
   targets=[sum(row)%2 for row in C]+[0]*len(J)+[0]*len(I)
   q0=next(r for r in P if r>N and r%12==7 and r not in seed+I and all(bit(r,p)==b for p,b in zip(seed+I,targets)))
   old=B+I;core_primes=old+J;baseline=core_primes+[q0];K,M,lam=matrices(baseline,len(B))
   smallK,smallM,_=matrices(old+[q0],len(B));u=len(old);c=len(core_primes)
   assert [row[:u] for row in M[:u]]==[row[:-1] for row in smallM[:-1]]
   assert rank([row[:u] for row in M[:u]])==u
   toggle=next(t for t in itertools.product([0,1],repeat=len(J)) if rank([[M[i][j]^(t[i-u] if i==j and i>=u else 0) for j in range(c)] for i in range(c)])==c)
   t=[0]*u+list(toggle)
   target=[bit(q0,p)^z for p,z in zip(core_primes,t)]
   q1=next(r for r in P if r>N and r%12==7 and r not in baseline and all(bit(r,p)==b for p,b in zip(core_primes,target)))
   final=core_primes+[q1];K1,M1,lam1=matrices(final,len(B));n=math.prod(old+[q1]);theta=math.prod(J)
   assert n*theta==math.prod(final) and n%12==(n*theta)%12==11
   assert len(set(final))==len(final) and q1!=q0 and q1>N
   assert rank([row[:-1] for row in M1[:-1]])==c
   for i in range(c):
    assert final[i]==baseline[i];counts['fixed_prime_values']+=1
    for j in range(c):
     assert M1[i][j]==M[i][j]^(t[i] if i==j else 0);counts['full_core_entries']+=1
   for i in range(u):
    for j in range(u):
     assert M1[i][j]==M[i][j];counts['old_core_entries']+=1
   beta=[int(i<len(B)) for i in range(len(final))]
   assert mv(K,beta)==mv(K1,beta)==[0]*len(final)
   span={tuple(a^(b*z) for z in beta) for a,b in itertools.product([0,1],repeat=2)}
   for v in itertools.product([0,1],repeat=len(final)):
    assert (mv(K1,v)==[0]*len(final))==(v in span)
    assert mv(K1,v)!=lam1
    counts['kernel_vectors']+=1
   counts['actual_replacements']+=1
result={'status':'PASS','checks':counts,'scope':'Actual q0 replacement, literal same old core, enlarged core unit, preserved beta equation and exact shared n/nθ products. No global Selmer/Kummer or rational-point existence claim.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
