# Exact rational boundary and same-x interval checks for all local counts.
from fractions import Fraction
from itertools import product
from math import prod, log
from random import Random
F=Fraction
rng=Random(960318326)
def weight(p): # signed deterministic test independent of divisor kernel
 return F((p*p+3*p)%31-15,7)
primes=(7,11,13,17,19,23,31,37,41,43,47,53,59)
for t in range(3):
 full=hits=samples=lost=kept=empty=0
 for _ in range(128):
  n=rng.randrange(7,94);W=30;b=1;q=rng.randrange(1,4);a=2;J=2+rng.randrange(2);M=1+rng.randrange(4)
  g=tuple(rng.randrange(J)-rng.randrange(J) for i in range(a))
  h=tuple((1+rng.randrange(M),1+rng.randrange(M)) for i in range(t))
  step=tuple((W*u-2*W*v)*(rng.randrange(2*M+1)-rng.randrange(2*M+1)) for u,v in h)
  off=[q*sum(i*j for i,j in zip(w[:a],g))+sum(i*j for i,j in zip(w[a:],step))
       for w in product(range(2),repeat=a+t) if rng.randrange(3)==0][:5]
  cells={}
  for x in range(1,n+1):
   k=tuple((x+u-1)//n for u in off)
   cells.setdefault(k, []).append(x)
  # deliberately include an empty fibre and use the totalized oldCell = 0.
  cells[tuple([max((abs(u)//n for u in off),default=0)+100]*len(off))]=[] if off else cells[()]
  K=lambda x: prod(weight(W*((x+u-1)%n+1)+b) for u in off)
  direct=sum((K(x) for x in range(1,n+1)),F(0))/n
  regroup=F(0);surv=F(0);mass=F(0);cap=max((abs(K(x)) for x in range(1,n+1)))
  for k,xs in cells.items():
   if not xs:
    empty+=1;continue
   assert xs==list(range(xs[0],xs[0]+len(xs)))
   e=tuple(u-v*n for u,v in zip(off,k));q0=len(xs)
   raw=[K(x) for x in xs]
   assay=[prod(weight(W*(x+u)+b) for u in e) for x in xs]
   assert raw==assay
   p0=[W*u+b for u in e]
   for i,j in product(range(len(e)),repeat=2):
    if i==j:continue
    D=W*(e[i]-e[j]);assert D==p0[i]-p0[j]
    for p in primes:
     assert (D%p==0)==((W*(xs[0]+e[i])+b-W*(xs[0]+e[j])-b)%p==0)
     if D and not D%p:assert p<=abs(D)<=2*W*n
     hits+=1
   co=F(q0,n);avg=sum(raw,F(0))/q0;regroup+=co*avg
   if q0**4>=n**3 and len(set(e))==len(e):
    surv+=co*avg;mass+=co;kept+=1
   else:lost+=1
   samples+=len(xs)
  assert direct==regroup and 0<=mass<=1 and abs(direct-surv)<=cap*(1-mass)
  full+=1
 print(t,'local blocks:',full,'whole samples',samples,'physical x iterations',hits,'modular hits',kept,'retained',lost,'clipped',empty,'empty')
