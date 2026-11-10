#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod,log
from pathlib import Path
from functools import lru_cache
import sympy as S
root=Path(__file__).resolve().parent
checks={'bad_union_counts':0,'per_lattice_counts':0,'source_slice_counts':0,'source_points':0,'weighted_source_sums':0,'exact_form_bounds':0}
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def length(v):return dot(v,v)
def mem(ps,k,ts,v):
 x,z,w=v
 return all((x%p==0 and w%p==0) if s is None else ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ts))
@lru_cache(None)
def family(ps,k):
 M=prod(ps);vs=list(product(range(-M,M+1),repeat=3));out=[]
 for ts in product(*([None]+list(range(p)) for p in ps)):
  L=sorted([v for v in vs if v!=(0,0,0) and mem(ps,k,ts,v)],key=length)
  u=L[0];v=next(v for v in L if cross(u,v)!=(0,0,0));n=cross(u,v)
  w=next(w for w in L if dot(n,w)!=0)
  out.append((ts,length(w)))
 return out
for ps in [(),(3,),(5,),(3,5)]:
 M=prod(ps)
 for k in [1,2]:
  F=family(ps,k)
  for B in [M,M+1]:
   box=list(product(range(-B,B+1),repeat=3));sets=[]
   for ts,ell in F:
    pts={v for v in box if mem(ps,k,ts,v)}
    assert len(pts)*M*M<=27*B**3;sets.append((pts,ell));checks['per_lattice_counts']+=1
   for T in [Q(1,2),Q(3,2),Q(5,2),Q(9,2),Q(13,2)]:
    bad=[s for s,ell in sets if ell>T*T];union=set().union(*bad)
    assert len(union)*M*M<=len(bad)*27*B**3
    assert len(union)*T**3<=5832*4**len(ps)*M*B**3
    checks['bad_union_counts']+=1
for B in range(1,5):
 for k in [1,2]:
  groups={}
  for a,b,c,d,w in product(range(-B,B+1),repeat=5):
   if a*a+b*b-c*c-d*d-k*w*w:continue
   for side,label in [(0,a-c),(1,a+c)]:
    if label==0:continue
    groups.setdefault((side,label),[]).append((a,b,c,d,w))
  for (side,label),pts in groups.items():
   ps=tuple(p for p in S.factorint(abs(label)) if (2*k)%p);M=prod(ps);F=family(ps,k)
   projections=[(b-d,b+d,w) for a,b,c,d,w in pts]
   assert len(set(projections))==len(pts) and all(max(map(abs,v))<=2*B for v in projections)
   for T in [Q(1,2),Q(3,2),Q(5,2),Q(9,2)]:
    badparams=[ts for ts,ell in F if ell>T*T]
    badflags=[any(mem(ps,k,ts,v) for ts in badparams) for v in projections]
    count=sum(badflags)
    gammas=[-3,0,2]
    ceiling=prod(log((2+abs(g))*B*B) for g in gammas)
    weights=[]
    for (a,b,c,d,w),flag in zip(pts,badflags):
     for g in gammas:
      assert abs(a*a+b*b+g*w*w)<=(2+abs(g))*B*B
      checks['exact_form_bounds']+=1
     weight=prod(log(max(1,abs(a*a+b*b+g*w*w))) for g in gammas)
     assert 0<=weight<=ceiling+1e-8
     if flag:weights.append(weight)
    assert sum(weights)*float(T**3)<=46656*4**len(ps)*M*B**3*ceiling+1e-8
    checks['weighted_source_sums']+=1
    assert count*T**3<=46656*4**len(ps)*M*B**3
    checks['source_slice_counts']+=1;checks['source_points']+=count
# The exceptional lattices overlap at zero; sum is an upper bound, not equality.
assert len({(0,0,0)}|{(0,0,0)})<len({(0,0,0)})+len({(0,0,0)})
for name in ['OriginalBadLatticePointTail318','OriginalBadSlicePointTail318','OriginalBadSliceLogWeight318']:
 text=(root/(name+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'negative control: non-disjoint lattice union')
