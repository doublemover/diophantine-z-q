"""Independent small finite tests of reassembly, residue powers and occupied cube gradients; not a prime count."""
from fractions import Fraction as F
from itertools import product
from math import gcd,prod
import json
def phi(n):return sum(gcd(a,n)==1 for a in range(n))
def bp(p,cs):
 return F(p,p-1)**len(cs)*F(sum(all((u+c*w*w)%p for c in cs)for u in range(p)for w in range(p)),p*p)
def crt(D,W,cs):
 q=D*W//gcd(D,W)
 choices=range(1,W+1);r=D//gcd(W,D)
 def mu(n,j):return F((3*(n%D)+j+1)%11,10) if gcd(n,D)==1 else F(0)
 def wt(u,w):return prod(mu(u+c*w*w,j)for j,c in enumerate(cs))
 Z=F(0)
 for b,c0 in product(choices,repeat=2):
  if not all(gcd(b+c*c0*c0,W)==1 for c in cs):continue
  Z+=sum(wt(W*x+b,W*y+c0)for x,y in product(range(r),repeat=2))
 Z*=F(W,phi(W))**len(cs)/q**2
 est=sum(wt(u,w)for u,w in product(range(D),repeat=2))*F(D,phi(D))**len(cs)/D**2
 for p in (2,3,5,7):
  if W%p==0 and D%p:est*=bp(p,cs)
 assert est==Z
 return str(Z)
cs=(0,1,6)
res={str((d,w)):crt(d,w,cs)for d,w in [(8,6),(12,30),(9,30),(16,30),(20,30)]}
for p in [5,7,11,13,17,19,23,29,31]:
 for coeff in [(0,2,3),(0,1,2,3),(0,1,3,5,7,11,13)]:
  b=len({c%p for c in coeff})
  assert bp(p,coeff)==F(p,p-1)**len(coeff)*F((p-1)*(p+1-b),p*p)
for p in (5,7,11):
 for q in (1,3,5,7):
  grads=[(1,*(q*t%p for t in v))for v in product((0,1),repeat=3)]
  assert len(set(grads))==(8 if q%p else 1)
print(json.dumps({'periodic-reassembly':res,'ordinary-factor-cases':27,'gradient-cases':12},indent=2))
