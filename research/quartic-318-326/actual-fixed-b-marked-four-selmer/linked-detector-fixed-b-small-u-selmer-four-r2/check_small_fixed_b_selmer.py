from fractions import Fraction as Q
from sympy import factorint
from math import prod
from flint import fmpz
from itertools import product
import json,sys
u=int(sys.argv[1]) if len(sys.argv)>1 else 258049
b=8912209*1185793321;t=Q(1,2399);L=Q(16*u**4+24*u*u+1,32*u*u)
E=(Q(0),b*t,-b*L)
F1=32*u*u;F2=(L+t).numerator;F3=L.numerator
S=sorted({2,2399,8912209,1185793321,*factorint(F1),*factorint(F2),*factorint(F3)})
S=[int(z) for z in S];G=[-1,*S];R=len(G)
print('u',u,'supports',S,'size',R,file=sys.stderr)
assert all(fmpz(p).is_prime() for p in S)
def vp(z,p):
 z=Q(z);a=z.numerator;d=z.denominator;e=0
 assert a
 while a%p==0:a//=p;e+=1
 while d%p==0:d//=p;e-=1
 return e,Q(a,d)
def loc(q,p):
 if p==-1:return int(q<0)
 e,U=vp(q,p)
 if p==2:
  v=U.numerator*pow(U.denominator,-1,8)%8
  return ((e%2)<<2)|{1:0,3:1,5:2,7:3}[v]
 V=U.numerator*pow(U.denominator,-1,p)%p
 wit=pow(V,(p-1)//2,p);assert wit in (1,p-1)
 return (e%2)*2+int(wit==p-1)
def row(ds,p):
 k=3 if p==2 else 1 if p==-1 else 2
 L=[loc(q,p) for q in ds];assert L[0]^L[1]^L[2]==0
 return L[0]|(L[1]<<k)
tors=[(Q(1),Q(1),Q(1))]
for i,j in enumerate(E):
 e=[j-c for c in E]; e[i]=prod(e[k] for k in range(3) if k!=i);tors.append(tuple(e))
def local_points(p):
 if p==-1:return {0:None,3:None}
 T={row(q,p):['T',i] for i,q in enumerate(tors)}
 if len(T)==(8 if p==2 else 4):return T
 offs=[i for i in range(1,257) if i%p]
 for k in sorted(range(-18,19),key=abs):
  for c,w in product(E,offs):
   x=c+w*(Q(1,p**(-k)) if k<0 else p**k)
   q=[x-d for d in E]
   if not all(q):continue
   ql=[loc(z,p) for z in q]
   if ql[0]^ql[1]^ql[2]:continue
   s=row(q,p)
   if s not in T:T[s]=[x.numerator,x.denominator]
   if len(T)==(8 if p==2 else 4):return T
 raise ValueError(('need new points',p,T))
GCM={}
for p in G:
 T=local_points(p);GCM[p]=T
 print('local',p,T,file=sys.stderr)
def rref(rows):
 W={}
 for x in rows:
  while x:
   j=x.bit_length()-1
   if j in W:x^=W[j]
   else:
    W[j]=x;break
 return W
def nulls(rows,d):
 R=rref(rows)
 out=[]
 for j in range(d):
  if j in R:continue
  q=1<<j
  for k,v in sorted(R.items()):
   if (q&v).bit_count()%2:q|=1<<k
  assert all(not ((q&v).bit_count()%2) for v in rows)
  out.append(q)
 return out
def pull_p(p,T):
 k=3 if p==2 else 1 if p==-1 else 2
 ann=nulls(list(T),2*k)
 W=[loc(q,p) for q in G];W=W+[a<<k for a in W]
 return [sum(((z&w).bit_count()%2)<<i for i,w in enumerate(W)) for z in ann]
eq=[]
for p,T in GCM.items():eq.extend(pull_p(p,T))
ker=nulls(eq,2*R)
def sqf(q):
 q=Q(q)
 assert q
 ans=-1 if q<0 else 1
 n,d=abs(q.numerator),q.denominator
 for p in S:
  e,u=vp(q,p)
  if e%2:ans*=p
  while n%p==0:n//=p
  while d%p==0:d//=p
 assert n==d==1
 return ans
def vv(q):
 return sum(((q<0) if p==-1 else q%p==0)<<j for j,p in enumerate(G))
def fromrow(m):
 d=[prod(p for j,p in enumerate(G) if (m>>(i*R+j))&1) for i in (0,1)]
 d.append(sqf(d[0]*d[1]))
 return d
assert len(rref(ker))==len(ker)
tg=[vv(sqf(q[0]))+(vv(sqf(q[1]))<<R) for q in tors]
mark=vv(b)
assert mark not in tg and all(not ((r&mark).bit_count()%2) for r in eq)
if u==258049:
 gamma=vv(2)<<R
 assert all(not ((r&z).bit_count()%2) for r in eq for z in [gamma,*tg])
 assert len(rref([mark,gamma,*tg]))==len(ker)==4
res=dict(u=u,b=b,lambda_=[L.numerator,L.denominator],roots=[[c.numerator,c.denominator] for c in E],
    support=G,local_images=GCM,tor=[list(map(sqf,q)) for q in tors],raw_mark=[b,1,b],null_basis=[fromrow(x) for x in ker],full_dim=len(ker),matrix=eq)
print(json.dumps(res,indent=2))
