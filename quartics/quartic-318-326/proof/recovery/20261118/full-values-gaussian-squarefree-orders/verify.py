"""Finite exact controls only. No finite calculation proves positive density."""
import json
from math import gcd,isqrt

def prime(n):return n>=2 and all(n%j for j in range(2,isqrt(n)+1))
def add(P,Q,A,p):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 if x==z and (y+w)%p==0:return None
 m=((3*x*x+A)*pow(2*y,-1,p) if x==z else (w-y)*pow(z-x,-1,p))%p
 s=(m*m-x-z)%p
 return s,(m*(x-s)-y)%p

def mul(k,P,A,p):
 Q=None
 while k:
  if k%2:Q=add(P,Q,A,p)
  P=add(P,P,A,p);k//=2
 return Q

def order(N,P,A,p):
 n=N
 for q in range(2,isqrt(N)+2):
  if prime(q):
   while n%q==0 and mul(n//q,P,A,p) is None:n//=q
 assert mul(n,P,A,p) is None
 for q in range(2,n+1):
  if n%q==0 and prime(q):assert mul(n//q,P,A,p) is not None
 return n

p=37537;assert prime(p) and p==81**2+176**2 and p%408==1 and p%7==3
seed=[]
for r,N,n in [(274,37376,1168),(p-274,37700,9425)]:
 A=-(3-r)**2;P=(1+r,2*r%p);assert (r*r-2)%p==0
 squares=[0]*p
 for y in range(p):squares[y*y%p]+=1
 assert 1+sum(squares[(x**3+A*x)%p] for x in range(p))==N
 assert order(N,P,A,p)==n and N%7
 seed.append(dict(r=r,count=N,point_order=n))
# Verify the complete local residue decomposition on all split units mod l^2.
split=[]
for l in (5,13,17,29):
 # Gaussian split ring is Z/l² times Z/l²; unit pair (x,y).
 z=l*l;units=[i for i in range(z) if i%l]
 alive=total=0
 for a in units:
  for b in units:
   U=(a-1)*(b-1);V=(a+1)*(b+1)
   bad=(U%z==0 or V%z==0 or gcd(gcd(U,V),l)!=1)
   classes=(any((a-h)%z==0 or (b-h)%z==0 or ((a-h)%l==0 and (b-h)%l==0) for h in (-1,1)) or any((a-h)%l==0 and (b+h)%l==0 for h in (-1,1)))
   assert bad==classes
   alive+=not bad;total+=1
 assert (total-alive)*(l-1)**2<=8*total
 split.append(dict(ell=l,good=alive,total=total))
inert=[]
for l in (3,7,11,19,23,31,43,47):
 bad=0
 for a in range(l):
  for b in range(l):
   if a==0 and b==0:continue
   X=((a-1)**2+b*b)*((a+1)**2+b*b)
   assert (X%l==0)==(b==0 and a in (1,l-1))
   bad+=X%l==0
 assert bad==2
 inert.append(l)
print(json.dumps(dict(seed=seed,split_local_tallies=split,inert_local_checks=inert),indent=2))
