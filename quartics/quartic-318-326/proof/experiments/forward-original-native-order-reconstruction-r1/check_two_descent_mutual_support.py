#!/usr/bin/env python3
"""Produce both actual finite descent supports, including nontrivial mutual rows."""
import itertools,json,math
from pathlib import Path
from sympy import primerange
P=list(primerange(5,1000000));counts={'simultaneous_producers':0,'nonzero_mutual_entries':0,'actual_core_entries':0,'both_supports':0,'coefficient_candidates':0,'coefficient_solutions':0}
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
def mats(primes,nb):
 n=len(primes);lam=[bit(3,p) for p in primes];s=[p//2%2 for p in primes];a=[int(i in [nb-1,n-1]) for i in range(n)]
 K=[[0 if i==j else bit(primes[j],primes[i]) for j in range(n)] for i in range(n)]
 for i in range(n):K[i][i]=sum(K[i])%2
 M=[[K[i][j]^(lam[i]*a[j]) for j in range(n)] for i in range(n)]
 return K,M,lam,s

def check_support(primes,nb,N):
 n=len(primes);K,M,lam,s=mats(primes,nb);beta=[int(i<nb) for i in range(n)]
 assert len(set(primes))==n and math.prod(primes)>N and math.prod(primes)%12==11
 assert mv(K,beta)==[0]*n and rank([r[:-1] for r in M[:-1]])==n-1
 span={tuple(c^(e*b) for b in beta) for c,e in itertools.product([0,1],repeat=2)}
 for v in itertools.product([0,1],repeat=n):
  Kv=mv(K,v)
  assert (Kv==[0]*n)==(v in span) and Kv!=lam
  counts['coefficient_candidates']+=2**(n+1)
  if any(x^(z*y) for x,z,y in zip(Kv,s,v)) or dot([x^y for x,y in zip(lam,s)],v):continue
  for u in itertools.product([0,1],repeat=n):
   Ku=mv(K,u)
   for delta in [0,1]:
    if all(x^(z*y)==delta*z for x,z,y in zip(Ku,lam,v)):
     assert delta==0 and not any(v) and u in span
     counts['coefficient_solutions']+=1
 counts['both_supports']+=1

for B in [[17],[17,73],[17,73,97],[17,73,97,193]]:
 assert math.prod(B)%24==17
 d=len(B)-1;C=[[int(b==i or b==d) for i in range(d)] for b in range(d+1)]
 Z=[q for q in P if q%24==1 and q not in B and all(bit(q,b)==0 for b in B)][:2]
 pattern=([1,1]+[0]*(len(B)-2)) if len(B)>1 else [0]
 T=[q for q in P if q%24==1 and q not in B and [bit(q,b) for b in B]==pattern][:2]
 for J in [[],Z[:1],T]:
  assert math.prod(J)%24==1 and not(set(B)&set(J))
  assert all(sum(bit(q,b) for q in J)%2==0 for b in B)
  assert all(sum(bit(b,q) for b in B)%2==0 for q in J)
  counts['nonzero_mutual_entries']+=sum(bit(q,b) for q in J for b in B)
  for N in [20,500]:
   forbidden={7,13,19,31,43,61,79};seed=B+J;I=[]
   for i in range(d):
    target=[C[b][i] for b in range(len(B))]+[0]*len(J)+[0]*len(I)
    q=next(q for q in P if q>N and q%12==1 and q not in seed+I and q not in forbidden and all(bit(q,p)==t for p,t in zip(seed+I,target)))
    I.append(q)
   target=[sum(row)%2 for row in C]+[0]*len(J)+[0]*len(I)
   q0=next(q for q in P if q>N and q%12==7 and q not in seed+I and q not in forbidden and all(bit(q,p)==t for p,t in zip(seed+I,target)))
   old=B+I;core=old+J;p0=core+[q0];K0,M0,_,_=mats(p0,len(B));_,S0,_,_=mats(old+[q0],len(B));u=len(old);c=len(core)
   assert [r[:u] for r in M0[:u]]==[r[:-1] for r in S0[:-1]]
   assert mv(K0,[int(i<len(B)) for i in range(len(p0))])==[0]*len(p0)
   toggle=next(t for t in itertools.product([0,1],repeat=len(J)) if rank([[M0[i][j]^(t[i-u] if i==j and i>=u else 0) for j in range(c)] for i in range(c)])==c)
   t=[0]*u+list(toggle);target=[bit(q0,p)^z for p,z in zip(core,t)]
   q1=next(q for q in P if q>N and q%12==7 and q not in p0 and q not in forbidden and all(bit(q,p)==z for p,z in zip(core,target)))
   p1=core+[q1];_,M1,_,_=mats(p1,len(B))
   for i in range(c):
    for j in range(c):
     assert M1[i][j]==M0[i][j]^(t[i] if i==j else 0)
     counts['actual_core_entries']+=1
   n=math.prod(old+[q1]);theta=math.prod(J)
   assert math.prod(p1)==n*theta and p1[:len(B)]==B and p1[u:c]==J
   check_support(old+[q1],len(B),N);check_support(p1,len(B),N)
   counts['simultaneous_producers']+=1
result={'status':'PASS','checks':counts,'scope':'Original mutual product squares, actual baseline prime family, same final q0 and n/nθ, both unit cores/kernels/local coefficient classifications. No Selmer/Kummer or rational-point existence claim.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
