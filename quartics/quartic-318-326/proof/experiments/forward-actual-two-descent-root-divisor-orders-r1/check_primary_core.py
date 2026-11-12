from itertools import product
import json
c=dict(finite_primary_cores=0,hom_core_preservation=0,alternating_pairings=0,rank_corank=0)
for a in range(7):
 for b in range(5):
  m,n=2**a,2**b
  G=list(product(range(m),range(n)))
  core=set(G)
  for k in range(max(a,b)+1):core&={(2**k*x%m,2**k*y%n) for x,y in G}
  assert core=={(0,0)};c['finite_primary_cores']+=1
  for d in range(4):
   h=2**d
   for u in range(h):
    if m*u%h:continue
    for v in range(h):
     if n*v%h:continue
     assert all((u*x+v*y)%h==0 for x,y in core)
     c['hom_core_preservation']+=1
for k in range(7):
 N=2**k
 for M in [1,2,4,8,16]:
  for u in range(M):
   if N*u%M:continue
   alternating=all(u*x*x%M==0 for x in range(N))
   if alternating:assert all(u*x*y%M==0 for x in range(N) for y in range(N))
   nondegenerate=all(any(u*x*y%M for y in range(N)) for x in range(1,N))
   if alternating and nondegenerate:assert N==1
   c['alternating_pairings']+=1
for r in range(2):
 for t in range(2):
  if 2**r*2**t==2:
   assert r+t==1;c['rank_corank']+=1
print(json.dumps({'status':'PASS','counts':c},indent=2))
