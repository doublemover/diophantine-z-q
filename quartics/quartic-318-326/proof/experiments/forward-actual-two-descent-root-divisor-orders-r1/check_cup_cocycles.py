#!/usr/bin/env python3
"""Exact finite F2/sign/cochain models only; not Lean, Galois or global duality."""
from itertools import product
import json
V=list(product(range(2),repeat=2))
def add(x,y):return tuple(a^b for a,b in zip(x,y))
def pair(x,y):return (x[0]*y[1])^(x[1]*y[0])
def quad(x):return x[0]*x[1]
counts={k:0 for k in ['sign_inverse','perfect_pairing','cocycle','self_boundary','cross_boundary','bilinear','restriction']}
for b in range(2):
 assert int((-1)**b==-1)==b
 counts['sign_inverse']+=1
chars={tuple(pair(x,y) for y in V) for x in V};assert len(chars)==4
for x,y,z in product(V,repeat=3):
 assert pair(add(x,y),z)==pair(x,z)^pair(y,z)
 assert pair(x,x)==0
 assert quad(add(x,y))^quad(x)^quad(y)==pair(x,y)
 counts['perfect_pairing']+=1
for r in range(4):
 G=list(product(range(2),repeat=r));zero=(0,)*r
 homs=[]
 for columns in product(V,repeat=r):
  a={g:tuple(sum(columns[i][j]*g[i] for i in range(r))%2 for j in range(2)) for g in G}
  homs.append(a)
 for a in homs:
  for g,h in product(G,repeat=2):
   assert quad(a[h])^quad(a[add(g,h)])^quad(a[g])==pair(a[g],a[h])
   counts['self_boundary']+=1
 for a,b in product(homs,repeat=2):
  for g,h in product(G,repeat=2):
   assert pair(a[h],b[h])^pair(a[add(g,h)],b[add(g,h)])^pair(a[g],b[g])==pair(a[g],b[h])^pair(b[g],a[h])
   counts['cross_boundary']+=1
   for x in V:
    assert pair(add(a[g],x),b[h])==pair(a[g],b[h])^pair(x,b[h])
    counts['bilinear']+=1
  for g,h,j in product(G,repeat=3):
   assert pair(a[h],b[j])^pair(a[add(g,h)],b[j])^pair(a[g],b[add(h,j)])^pair(a[g],b[h])==0
   counts['cocycle']+=1
  for t in G:
   phi={0:zero,1:t}
   ar={i:a[phi[i]] for i in range(2)};br={i:b[phi[i]] for i in range(2)}
   for g,h in product(range(2),repeat=2):
    assert pair(ar[g],br[h])==pair(a[phi[g]],b[phi[h]])
    assert quad(ar[h])^quad(ar[g^h])^quad(ar[g])==pair(ar[g],ar[h])
    counts['restriction']+=1
print(json.dumps({'status':'PASS','scope':__doc__,'tested_groups':'F2^r, 0<=r<=3; all binary-plane-valued homomorphisms','counts':counts},indent=2))
