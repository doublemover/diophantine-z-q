from fractions import Fraction as F
from math import gcd
from functools import lru_cache
from collections import Counter
import json
N=48
units=[a for a in range(N) if gcd(a,N)==1]
def norm(c,d): return min(((u*c)%N,(u*d)%N) for u in units)
keys=sorted({norm(c,d) for c in range(N) for d in range(N) if gcd(gcd(c,d),N)==1})
I={a:i for i,a in enumerate(keys)}; m=len(keys)
def idx(c,d):return I[norm(c,d)]
def egcd(a,b):
 if not b:return (a,1,0)
 g,x,y=egcd(b,a%b);return(g,y,x-a//b*y)
def endpoints(c,d):
 if c==0:return (None,F(0))
 while gcd(c,d)!=1:d+=N
 g,a,b=egcd(d,c);assert g==1
 return (F(a,c),F(-b,d) if d else None)
@lru_cache(None)
def path(x):
 C=Counter()
 if x is None:return C
 xa,xb=1,0; ya,yb=0,1
 a,b=x.numerator,x.denominator
 while b:
  q,r=divmod(a,b)
  c,d=q*xa+ya,q*xb+yb
  e=c*xb-d*xa
  assert e in (1,-1)
  if e==1:C[idx(d,xb)]+=1
  else:C[idx(xb,d)]-=1
  a,b=b,r
  ya,yb,xa,xb=xa,xb,c,d
 assert F(xa,xb)==x
 return C

def column(*rows):
 z=[0]*m
 for i,j in rows:z[i]+=j
 return z
rows=[]
for i,(c,d) in enumerate(keys):
 rows.append(column((i,1),(idx(d,-c),1)))
 rows.append(column((i,1),(idx(d,-c-d),1),(idx(-c-d,c),1)))
 rows.append(column((i,1),(idx(c,-d),-1)))
 x,y=endpoints(c,d)
 T=[-a for a in column((i,-4))]
 # Supposed T_11 f = -4 f, so sum(neighbor path)+4 * symbol =0.
 p=11
 for k in [-1]+list(range(p)):
  g=lambda x:None if x is None else p*x if k<0 else (x+k)/p
  for j,n in path(g(x)).items():T[j]+=n
  for j,n in path(g(y)).items():T[j]-=n
 rows.append(T)

def solve(A):
 C={}
 for a in A:
  a=list(map(F,a))
  for p,b in sorted(C.items()):
   t=a[p]
   if t:a=[x-t*y for x,y in zip(a,b)]
  p=next((j for j,v in enumerate(a) if v),None)
  if p is not None:
   v=a[p]; C[p]=[x/v for x in a]
 return C
B=solve(rows)
free=list(set(range(m))-set(B))
assert len(free)==1,(m,len(B),free)
v=[F(0)]*m;v[free[0]]=1
for i,x in sorted(B.items(),reverse=True):v[i]=-sum(v[j]*x[j] for j in range(i+1,m))
assert all(sum(x*y for x,y in zip(a,v))==0 for a in rows)
value=lambda x:sum(v[j]*n for j,n in path(x).items())
a0=value(F(0))
assert a0!=0
f=241
w=sum((1 if pow(a,(f-1)//2,f)==1 else -1)*value(F(a,f)) for a in range(1,f))
assert m==96 and len(B)==95 and a0==1 and w==64
def ap(p):
 r=[0]*p
 for y in range(p):r[y*y%p]+=1
 return p-sum(r[x*(x+1)*(x-3)%p] for x in range(p))
assert ap(11)==-4 and ap(29)==6 and pow(241%29,14,29)==1
print(json.dumps(dict(level=N,manin_classes=m,relation_rows=len(rows),rank=len(B),free=free,
  a11=ap(11),real_winding=str(a0),winding_twisted_241=str(w),ratio=str(w/a0),
  exact_symbol_values=[str(t) for t in v],a29=ap(29)),indent=2))
