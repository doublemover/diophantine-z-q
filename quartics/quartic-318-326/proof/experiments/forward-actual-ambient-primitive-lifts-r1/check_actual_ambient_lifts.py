#!/usr/bin/env python3
import itertools as it,json,collections
C=collections.Counter()
def Q(k,x):
 a,b,c,d,w=x;return a*a+b*b-c*c-d*d-k*w*w
for m in range(1,18):
 for p in range(1,12):
  digits=[(y%m,y//m) for y in range(m*p)]
  assert len(set(digits))==m*p
  assert set(digits)==set(it.product(range(m),range(p)))
  for y,(x,h) in enumerate(digits):
   assert x+m*h==y and y%m==x
   if m%p==0:assert x%p==y%p;C['original_prime_reduction']+=1
   C['scalar_inverses']+=1
  for x in range(m):
   assert {x+m*h for h in range(p)}=={y for y in range(m*p) if y%m==x}
   C['all_scalar_fibers']+=1
# Independently enumerate ambient coordinate fibers from actual modular reduction,
# then compare the Cartesian reconstruction, both inverses and original Q test.
for p,m in [(2,2),(3,3),(3,9),(5,5),(3,6)]:
 for k in [1,2,318,326,-1]:
  bases=[x for x in it.product(range(m),repeat=5) if Q(k,x)%m==0]
  if len(bases)>13:bases=bases[:5]+bases[len(bases)//2:len(bases)//2+4]+bases[-4:]
  fibers={}
  for x in bases:
   scalar=[[y for y in range(m*p) if y%m==xx] for xx in x]
   ambient=set(it.product(*scalar))
   images={tuple(xx+m*h for xx,h in zip(x,hs)):hs for hs in it.product(range(p),repeat=5)}
   assert len(images)==p**5 and set(images)==ambient
   for y,hs in images.items():
    assert tuple(v//m for v in y)==hs and tuple(v%m for v in y)==x
    assert all(a%p==b%p for a,b in zip(x,y))
    C['coordinate_inverses_and_reduction']+=1
   good={y for y in ambient if Q(k,y)%(m*p)==0}
   allowed={y for y in images if Q(k,y)%(p*m)==0}
   assert good==allowed
   fibers[x]=good
   if p%2 and k%p and any(v%p for v in x):
    assert len(good)==p**4
    assert all(any(v%p for v in y) for y in good)
    C['all_primitive_quadric_fibers']+=1
   C['quadric_fiber_equivalences']+=1
  if p%2 and k%p:
   primitive=[x for x in bases if any(v%p for v in x)]
   for R in [[],primitive[:1],primitive[::2],primitive]:
    actual={y for x in R for y in fibers[x]}
    assert len(actual)==len(R)*p**4
    assert all(tuple(v%m for v in y) in R for y in actual)
    assert all(any(v%p for v in y) for y in actual)
    C['arbitrary_subset_counts']+=1
print(json.dumps({'status':'PASS',**C},sort_keys=True))
