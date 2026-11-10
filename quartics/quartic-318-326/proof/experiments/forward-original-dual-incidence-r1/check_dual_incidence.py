#!/usr/bin/env python3
from itertools import product
import math,json

def gen(k,t,p):return (0,1,0) if t is None else(1,k*t*t%p,t)
def dot(v,u):return sum(a*b for a,b in zip(v,u))
def code(k,t,u,p):
 x,z,w=u;return(x%p,w%p) if t is None else((z-k*t*t*x)%p,(w-t*x)%p)
local=0
for p in(2,3,5,7,11):
 for k in(1,2,3):
  if k%p==0:continue
  dirs=[None,*range(p)]
  for v in product(range(p),repeat=3):
   count=sum(dot(v,gen(k,t,p))%p==0 for t in dirs)
   assert count==p+1 if v==(0,0,0) else count<=2
   local+=1
ps=(3,5);M=15;k=1;dirs=list(product(*[[None,*range(p)] for p in ps]))
lattices={t:[u for u in product(range(M),repeat=3) if all(code(k,s,u,p)==(0,0) for s,p in zip(t,ps))] for t in dirs}
checks=0
for v in product(range(M),repeat=3):
 count=0
 for ts in dirs:
  left=all(dot(v,u)%M==0 for u in lattices[ts])
  right=all(dot(v,gen(k,t,p))%p==0 for t,p in zip(ts,ps))
  assert left==right
  count+=left;checks+=1
 zero=math.prod(p if all(c%p==0 for c in v) else 1 for p in ps)
 assert count<=2**len(ps)*zero
assert sum(dot((0,1,0),gen(0,t,5))%5==0 for t in[None,*range(5)])==5>2
assert sum(dot((0,0,0),gen(1,t,5))%5==0 for t in[None,*range(5)])==6>2
print(json.dumps({'local_dual_vector_counts':local,'actual_global_integer_duality_checks':checks,'actual_global_vector_incidence_bounds':M**3,'negative_controls':['zero_coefficient','zero_vector_exception']},sort_keys=True))
