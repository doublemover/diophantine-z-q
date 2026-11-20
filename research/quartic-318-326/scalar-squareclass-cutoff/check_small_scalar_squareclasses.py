#!/usr/bin/env python3
"""Exact bound on scalar squareclasses, no evaluation grid in a."""
from collections import Counter
from itertools import product,combinations
from functools import lru_cache
from math import prod,isqrt
import json
f=((7446,661),(7446,1861),(29784,7445),(476544,119479))
check_mods=(8,3,17,5,7)
@lru_cache(None)
def masks_at(p):
 masks={sum(1<<i for i,(A,B) in enumerate(f) if (A*r*(r+1)+B)%p==0) for r in range(p)}
 return sorted({s for m in masks for s in range(16) if s&m==s})
@lru_cache(None)
def rows_mod(q):
 ts={a*(a+1)%q for a in range(q)}
 return [tuple((a*t+b)%q for a,b in f) for t in ts]
@lru_cache(None)
def sqscaled(q,z):
 return {z*a*a%q for a in range(q)}
def check(fs):
 ps=set(fs)|{7,11,359,4801}
 decomp=[(p,[m for m in masks_at(p) if m.bit_count()%2==((p in fs)^(p==11))]) for p in sorted(ps)]
 if any(not m for _,m in decomp):return -1,[]
 S=[tuple(prod(p for (p,_),m in zip(decomp,mm) if m>>i&1) for i in range(4)) for mm in product(*(ms for _,ms in decomp))]
 for q in check_mods:
  R=rows_mod(q);out=[]
  for a in S:
   cells=[sqscaled(q,x%q) for x in a]
   if any(all(x in c for x,c in zip(g,cells)) for g in R):
    out.append(a)
  S=out
  if not S:return q,[]
 return 0,S
def fac(k):
 a=k;out=[]
 for p in range(2,isqrt(k)+1):
  if a%p==0:
   a//=p;out.append(p)
   if a%p==0:return None
 if a>1:out.append(a)
 return tuple(out)
def run(B):
 # (g_i slope,constant) determinants have only these prime factors.
 m=(2,3,5,7,17,73,359,4801)
 for (A,b),(B0,d) in combinations(f,2):
  g=abs(A*d-B0*b)
  for p in m:
   while not g%p:g//=p
  assert g==1
 assert all(all(b%p for A,b in f) for p in (2,3,17,73))
 assert all(all((A*r*(r+1)+b)%5 for A,b in (f[0],f[1],f[3])) for r in range(5))
 assert all((f[2][0]*r*(r+1)+f[2][1])%11 for r in range(11))
 for q0 in (359,4801):
  assert all(q0%d for d in range(2,isqrt(q0)+1))
 # Exact expansion at the coefficient level, not testing integer samples.
 row=[1]
 for A,b in f:
  out=[0]*(len(row)+1)
  for i,v in enumerate(row):
   out[i]+=b*v;out[i+1]+=A*v
  row=out
 R=(4376874610839020,101783690143177584,800910366213064752,2642145132961084032,3147690941013049344)
 assert [4*z for z in row]==list(R)
 c=Counter();S=[]
 for k in range(1,B+1,24):
  if k%17==0 or k%73==0:continue
  fs=fac(k)
  if fs is None:continue
  if not any(prod(ds)%24 in (5,19) for l in range(len(fs)+1) for ds in combinations(fs,l)):
   c['coset']+=1;continue
  e,W=check(fs)
  c[e]+=1
  if W:S.append((k,fs,W))
 status=dict(bound=B, total_candidates=sum(c.values()), rejects={str(k):v for k,v in c.items()}, survivors=S)
 print(json.dumps(status,sort_keys=True,indent=2))
 return S
if __name__=='__main__':assert not run(100000)
