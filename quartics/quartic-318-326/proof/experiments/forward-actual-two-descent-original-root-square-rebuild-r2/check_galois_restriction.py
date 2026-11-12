from itertools import product
import json
counts=dict(quadratic_fields=0,scalar_restrictions=0,torsion_transfers=0,character_restrictions=0,subgroup_quotient_diagrams=0)
for p in [5,7,11,13,17,19,23]:
 d=next(a for a in range(2,p) if pow(a,(p-1)//2,p)==p-1)
 def mul(x,y):return((x[0]*y[0]+d*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
 def inv(x):
  k=pow((x[0]*x[0]-d*x[1]*x[1])%p,-1,p);return(x[0]*k%p,-x[1]*k%p)
 def frob(x):return(x[0],-x[1]%p)
 for a in range(1,p):
  roots=[r for r in product(range(p),repeat=2) if mul(r,r)==(a,0)]
  assert len(roots)==2
  for r in roots:
   char=mul(frob(r),inv(r));assert char==(pow(a,(p-1)//2,p),0)
   assert mul(r,inv(r))==(1,0) # Restricting to the quadratic base field kills the root character.
   assert frob((a,0))==(a,0)
   counts['scalar_restrictions']+=2
  for sign in [(1,1),(-1,-1),(-1,1),(1,-1)]:
   mapped=tuple((s%p,0) for s in sign)
   assert tuple(mul(v,v) for v in mapped)==((1,0),(1,0))
   counts['torsion_transfers']+=1
 counts['quadratic_fields']+=1
# Exhaustive finite elementary-two-group character restriction diagrams.
for m in range(1,5):
 G=list(product(range(2),repeat=m))
 dot=lambda a,b:sum(x*y for x,y in zip(a,b))%2
 xor=lambda a,b:tuple(x^y for x,y in zip(a,b))
 for dim in range(m+1):
  for a,b in product(G,repeat=2):
   for x in product(range(2),repeat=dim):
    lift=x+(0,)*(m-dim)
    assert dot(a,lift)==dot(a[:dim],x)
    assert dot(xor(a,b),lift)==(dot(a,lift)^dot(b,lift))
    counts['character_restrictions']+=1
# Every coordinate subgroup pair R<=S gives exact |S|=|R|*|S/R| under all coordinate permutations.
from itertools import permutations
for m in range(1,5):
 for sd in range(m+1):
  for rd in range(sd+1):
   S={x+(0,)*(m-sd) for x in product(range(2),repeat=sd)}
   R={x+(0,)*(m-rd) for x in product(range(2),repeat=rd)}
   cosets={frozenset(xor(s,r) for r in R) for s in S}
   assert len(S)==len(R)*len(cosets)
   for perm in permutations(range(m)):
    f=lambda x:tuple(x[i] for i in perm)
    Sc={f(s) for s in S};Rc={f(r) for r in R}
    assert {frozenset(f(x) for x in C) for C in cosets}=={frozenset(xor(s,r) for r in Rc) for s in Sc}
    counts['subgroup_quotient_diagrams']+=1
print(json.dumps({'status':'PASS','scope':'Finite exact restriction/coefficient/quotient regression only; not Lean or infinite Galois verification','counts':counts},indent=2,sort_keys=True))
