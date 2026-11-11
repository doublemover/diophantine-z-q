from itertools import product
import json
counts=dict(fields=0,root_pairs=0,kernel_cases=0,multiplicativity=0,hilbert_coboundaries=0,rational_squares=0,characters=0,finite_factor_values=0)
for p in [5,7,11,13,17,19,23,29,31]:
 d=next(d for d in range(2,p) if pow(d,(p-1)//2,p)==p-1)
 def mul(a,b):return((a[0]*b[0]+d*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
 def inv(a):
  q=pow((a[0]*a[0]-d*a[1]*a[1])%p,-1,p)
  return(a[0]*q%p,-a[1]*q%p)
 def div(a,b):return mul(a,inv(b))
 def F(a):return(a[0],-a[1]%p)
 U=[a for a in product(range(p),repeat=2) if a!=(0,0)]
 chars={}
 for a in range(1,p):
  roots=[r for r in U if mul(r,r)==(a,0)];assert len(roots)==2
  v=[div(F(r),r) for r in roots];assert v[0]==v[1] and v[0] in[(1,0),(p-1,0)]
  chars[a]=v[0];counts['root_pairs']+=4
  assert (v[0]==(1,0))==any(b*b%p==a for b in range(1,p));counts['kernel_cases']+=1
 for a,b in product(range(1,p),repeat=2):
  assert chars[a*b%p]==mul(chars[a],chars[b]);counts['multiplicativity']+=1
 assert set(chars.values())=={(1,0),(p-1,0)}
 for eps in [1,p-1]:
  bs=[b for b in U if div(F(b),b)==(eps,0)];assert len(bs)==p-1
  for b in bs:
   a=mul(b,b);assert a[1]==0 and a[0]!=0 and chars[a[0]]==(eps,0)
   counts['hilbert_coboundaries']+=1;counts['rational_squares']+=1
 counts['fields']+=1
for dim in range(1,7):
 group=list(product([0,1],repeat=dim))
 for ch in group:
  f=lambda x:sum(a*b for a,b in zip(ch,x))%2
  support=[i for i,c in enumerate(ch) if c]
  for g in group:
   restriction=tuple(g[i] for i in support)
   assert sum(restriction)%2==f(g);counts['finite_factor_values']+=1
  counts['characters']+=1
print(json.dumps({'status':'PASS','scope':'Exact finite-field scalar Kummer and finite-sign factorization regression; not Qbar topology or a Lean build','counts':counts},sort_keys=True,indent=2))
