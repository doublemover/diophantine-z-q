from itertools import product
from random import Random
from collections import Counter
from math import isqrt
r=Random(654318326)
count=act=shared=0
for _ in range(1000):
 a,t,b,s=r.randrange(3),r.randrange(3),r.randrange(1,4),r.randrange(1,4)
 W,D,C,n,M,q,J=r.choice([2,6,30]),3,r.randrange(1,4),r.randrange(10,80),r.randrange(1,4),r.randrange(1,5),r.randrange(1,6)
 C=max(C,(W*M*M+n-1)//n)
 if q*J>n: continue
 S=[[r.randrange(-D,D+1) for k in range(s)] for j in range(b)]
 if any(not any(l) for l in S):continue
 g=[[r.randrange(J) for e in range(2)] for i in range(a)]
 h=[[r.randrange(1,M+1) for k in range(s)] for z in range(t)]
 ends=[[[r.randrange(-M,M+1) for e in range(2)] for j in range(b)] for z in range(t)]
 verts=list(product((0,1),repeat=a+t*b))
 verts=r.sample(verts,min(len(verts),5))
 def off(v):
  return q*sum(f*(z[1]-z[0]) for f,z in zip(v[:a],g))+sum(
   v[a+k*b+j]*W*sum(u*w for u,w in zip(S[j],h[k]))*(ends[k][j][1]-ends[k][j][0])
   for k in range(t) for j in range(b))
 offsets=[off(v) for v in verts]; cap=a+2*t*b*s*D*C
 assert all(abs(i)<=cap*n for i in offsets)
 keys=Counter(tuple((x+y-1)//n for y in offsets) for x in range(1,n+1))
 assert sum(keys.values())==n
 if t and b>1:shared+=1
 for key,mass in keys.items():
  xs=[x for x in range(1,n+1) if tuple((x+y-1)//n for y in offsets)==key]
  assert xs==list(range(xs[0],xs[0]+mass))
  for i,j in product(range(len(verts)),repeat=2):
   if i==j:continue
   dw=W*(offsets[i]-offsets[j]-n*(key[i]-key[j]))
   for x in (xs[0],xs[-1]):
    A=W*(x+offsets[i]-n*key[i])+1
    B=W*(x+offsets[j]-n*key[j])+1
    assert A-B==dw and 0<A<=W*n+1 and 0<B<=W*n+1
   count+=1
 act+=1
print('accepted-wrap models',act,'shared multi-axis active',shared,'physical cell pairs',count)
