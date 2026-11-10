#!/usr/bin/env python3
from itertools import product
from math import prod
from fractions import Fraction as Q
from pathlib import Path
root=Path(__file__).resolve().parent
checks={'original_lattice_families':0,'primal_vectors':0,'dual_vectors':0,'score_norm_pairs':0}
def length(v):return sum(x*x for x in v)
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def grows(bs,v):
 if v==(0,0,0):return False
 if not bs:return True
 if len(bs)==1:return cross(bs[0],v)!=(0,0,0)
 return dot(cross(bs[0],bs[1]),v)!=0
for ps in [[],[3],[5],[3,5]]:
 M=prod(ps);vs=list(product(range(-M,M+1),repeat=3))
 for k in [1,2]:
  for ts in product(*([None]+list(range(p)) for p in ps)):
   primal=[v for v in vs if all((v[0]%p==0 and v[2]%p==0) if s is None else ((v[1]-k*s*s*v[0])%p==0 and (v[2]-s*v[0])%p==0) for p,s in zip(ps,ts))]
   dual=[v for v in vs if v!=(0,0,0) and all((v[1]%p==0) if s is None else (v[0]+k*s*s*v[1]+s*v[2])%p==0 for p,s in zip(ps,ts))]
   assert dual
   shortest=min(dual,key=length);n=length(shortest)
   assert 0<n<=M*M and all(n<=length(v) for v in dual)
   bs=[]
   for v in sorted(primal,key=length):
    if grows(bs,v):bs.append(v)
    if len(bs)==3:break
   assert len(bs)==3
   score=max(map(length,bs));assert 0<score<=M*M
   shorter=[]
   for v in primal:
    if length(v)<score and grows(shorter,v):shorter.append(v)
   assert len(shorter)<3
   assert all(length(v)<=score for v in bs)
   checks['original_lattice_families']+=1
   checks['primal_vectors']+=len(primal);checks['dual_vectors']+=len(dual)
for v in product(range(-2,3),repeat=3):
 for u in [(0,0,0),(1,0,0),(1,1,1),(2,-1,0)]:
  assert (length(v)<=length(u))==(Q(length(v))<=Q(length(u)))
  checks['score_norm_pairs']+=1
# Rank alone does not fix the third minimum: a thin lattice has rank3.
assert max(map(length,[(1,0,0),(0,1,0),(0,0,100)]))==10000
for name in ['OriginalIntegerSquaredNorm318','OriginalAttainedMinima318']:
 text=(root/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'negative control: rank3 does not control the third minimum')
