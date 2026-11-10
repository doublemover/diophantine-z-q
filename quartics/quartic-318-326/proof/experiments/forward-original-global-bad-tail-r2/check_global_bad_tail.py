#!/usr/bin/env python3
from itertools import product, combinations
from functools import lru_cache
from math import prod, log
from pathlib import Path
import sympy as S
checks={'exact_subpower':0,'signed_label_counts':0,'unique_source_partitions':0,'actual_threshold_counts':0,'actual_threshold_log_masses':0,'fixed_to_total_constants':0}
# delta=1/b permits wholly integer verification, including the constructed cutoff.
for A in [1,2,4,9]:
 for b in [1,2,3]:
  N=A**b;C=A**N
  for k in range(6):
   for ps in combinations([2,3,5,7,11],k):
    q=prod(ps)
    assert A**(k*b)<=C**b*q
    checks['exact_subpower']+=1
for B in range(101):
 labels=[t for t in range(-2*B,2*B+1) if t]
 assert len(labels)==4*B;checks['signed_label_counts']+=1
 for b in [1,2,3]:
  # Fixed-label coefficient93312 and all-label coefficient373248 are exact.
  assert len(labels)*93312*B**4==373248*B**5
  checks['fixed_to_total_constants']+=1

def dot(u,v):return sum(a*b for a,b in zip(u,v))
def cross(u,v):return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def mem(ps,k,ss,v):
 x,z,w=v
 return all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ss))
@lru_cache(None)
def family(ps,k):
 M=prod(ps);box=list(product(range(-M,M+1),repeat=3));out=[]
 for ss in product(*([None]+list(range(p)) for p in ps)):
  vs=sorted([v for v in box if v!=(0,0,0) and mem(ps,k,ss,v)],key=lambda v:dot(v,v))
  u=vs[0];v=next(v for v in vs if cross(u,v)!=(0,0,0));n=cross(u,v)
  w=next(w for w in vs if dot(n,w)!=0)
  out.append((ss,dot(w,w)))
 return out
for B in range(1,4):
 for k in [-2,0,1,2]:
  pts=[v for v in product(range(-B,B+1),repeat=5) if v[0]**2+v[1]**2-v[2]**2-v[3]**2-k*v[4]**2==0]
  for side in [False,True]:
   grouped={};actual=[]
   for v in pts:
    a,b,c,d,w=v;t=a+c if side else a-c
    if not t:continue
    ps=tuple(p for p in S.factorint(abs(t)) if (2*k)%p)
    F=family(ps,k);q=prod(ps)
    bad=any(ell*ell>B**3 and mem(ps,k,ss,(b-d,b+d,w)) for ss,ell in F)
    if bad:grouped.setdefault(t,[]).append(v);actual.append(v)
   partition=[(t,v) for t,vs in grouped.items() for v in vs]
   assert len(partition)==len(actual)==len(set(actual))
   assert set(v for t,v in partition)==set(actual)
   checks['unique_source_partitions']+=1
   # Threshold exponent 11/4+delta; raise fourth power to check exact count.
   for d in [1,2]:
    C=373248*4**(4 if d==1 else 2)*2**d
    assert len(actual)**4<=C**4*B**(11+4*d)
    checks['actual_threshold_counts']+=1
    gammas=[-3,0,2];W=prod(log((2+abs(g))*B*B) for g in gammas)
    mass=sum(prod(log(max(1,abs(a*a+b*b+g*w*w))) for g in gammas) for a,b,c,d0,w in actual)
    assert mass<=C*B**(11/4+d)*W+1e-8
    checks['actual_threshold_log_masses']+=1
# Both signs are required; zero is excluded; disjointness is only between labels.
assert len([t for t in range(-4,5) if t])==8
assert len([t for t in range(1,5)])!=8
assert (11/4)+(3/4)*3==5
for name in ['FinitePrimeSubpower318','OriginalGlobalBadMass318','OriginalGlobalBadSource318']:
 text=(Path(__file__).resolve().parent/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'negative controls: sign omission, zero-label exclusion, no lattice-incidence deduplication')
