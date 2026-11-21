from fractions import Fraction as F
from math import prod,gcd,lcm
from itertools import product
from sympy.abc import x,y,z
from sympy import factorint
from sympy.solvers.diophantine.diophantine import diop_ternary_quadratic_normal as tq
import json,sys
pA=415721; qA,q1,q2=map(int,sys.argv[1:])
a,b=pA*qA,q1*q2;D=a*b
s,t=F(-32,407),F(1,2399)
e=[F(0),s*D,t*D]
alpha=[D,b,a]; u=[2399*a*q1,2399*q1,a]; v=[11,5*2399,5*11*2399]
S=(2,3,5,7,11,13,17,19,23,29,37,2399,pA,qA,q1,q2)
def norm(vals):
 k=lcm(*(q.denominator for q in vals))
 ans=[int(q*k) for q in vals]
 g=gcd(*ans)
 return [n//g for n in ans]
def vmod(n,p):
 q=F(n)
 if not q:raise ValueError('zero')
 n,d=q.numerator,q.denominator;k=0
 while n%p==0:n//=p;k+=1
 while d%p==0:d//=p;k-=1
 return k,F(n,d)
def unit_mod(x,M):
 x=F(x)
 return x.numerator*pow(x.denominator,-1,M)%M
def leg(a,p):return {0:0,1:1,p-1:-1}[pow(a%p,(p-1)//2,p)]
def sqrtn_mod(a,p):
 a%=p
 assert leg(a,p)==1
 q=p-1;e=0
 while q%2==0:q//=2;e+=1
 z=next(z for z in range(2,p) if leg(z,p)==-1)
 u,t,r=pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
 while t!=1:
  i=next(j for j in range(e) if pow(t,2**j,p)==1)
  z=pow(u,2**(e-i-1),p)
  r=r*z%p;t=t*z*z%p;u=z*z%p;e=i
 assert r*r%p==a
 return r
def sqrt_unit(a,p,N):
 a=unit_mod(a,p**N)
 if p==2:
  if a%8!=1:return None
  r=1
  for k in range(3,N):
   if (r*r-a)%2**(k+1):r+=2**(k-1)
   assert (r*r-a)%2**(k+1)==0
  return r
 if leg(a,p)!=1:return None
 r=sqrtn_mod(a,p);m=p
 for k in range(1,N):
  r+=m*((a-r*r)//m*pow(2*r,-1,p)%p)
  m*=p
 assert (r*r-a)%m==0
 return r
def power(p,i):return F(p**i) if i>=0 else F(1,p**(-i))
def sqrt_qp(x,p,N):
 k,x0=vmod(x,p)
 if k%2:return None
 y=sqrt_unit(x0,p,N)
 return None if y is None else (y*power(p,k//2), k//2+N-(p==2))
def symbol(x,y,p):
 a,x0=vmod(x,p)
 b,y0=vmod(y,p)
 if p==2:
  r=unit_mod(x0,8);s=unit_mod(y0,8)
  return (-1)**(((r-1)*(s-1)//4 + a*(s*s-1)//8 + b*(r*r-1)//8)%2)
 return (-1)**(a*b*((p-1)//2)%2)*leg(unit_mod(x0,p),p)**(b%2)*leg(unit_mod(y0,p),p)**(a%2)
def tangent(d):
 Q=[]
 for i in range(3):
  j,k=[j for j in range(3) if j!=i]
  co=norm([F(d[j]),F(-d[k]),e[j]-e[k]])
  sf=[];sq=[]
  for c in co:
   fac=factorint(abs(c))
   sf.append(prod(int(f) for f,k in fac.items() if k%2)*(1 if c>0 else -1))
   sq.append(prod(int(f)**(k//2) for f,k in fac.items()))
  gg=gcd(*sf); sf=[n//gg for n in sf]
  ps=[gcd(sf[1],sf[2]),gcd(sf[0],sf[2]),gcd(sf[0],sf[1])]
  ds=[n*p*p//prod(ps) for n,p in zip(sf,ps)]
  assert all(gcd(d,c)==1 for i,d in enumerate(ds) for c in ds[:i])
  EQ=ds[0]*x*x+ds[1]*y*y+ds[2]*z*z
  R=tuple(map(int,tq(EQ)))
  assert sum(c*h*h for c,h in zip(ds,R))==0
  p=tuple(norm([F(p*h,u) for p,h,u in zip(ps,R,sq)]))
  assert gcd(*p)==1 and sum(c*h*h for c,h in zip(co,p))==0 and all(p)
  Q.append([i,j,k,list(co),list(p)])
 return Q
def good_sample(center,vv,u,p):
 return center+power(p,vv)*u
def local_qpoint(d,q,ps,p):
 if all(vmod(t,p)[0]%2==0 and sqrt_unit(vmod(t,p)[1],p,8) is not None for t in q):return [p,1,None]
 for vv,center,u in product(range(-10,12),e,range(1,65)):
  px=good_sample(center,vv,u,p)
  if px in e:continue
  square=[(px-ee)/dd for ee,dd in zip(e,d)]
  roots=[sqrt_qp(c,p,18) for c in square]
  if not all(r is not None for r in roots):continue
  zs=[r[0] for r in roots]; prec=[r[1] for r in roots]
  ts=[]; sy=[]
  for i,j,k,C,Y in ps:
   c=[c*y for c,y in zip(C,Y)]
   val=c[0]*zs[j]+c[1]*zs[k]+c[2]
   if not val:break
   eb=min(vmod(c[0],p)[0]+prec[j],vmod(c[1],p)[0]+prec[k])
   if eb<vmod(val,p)[0]+(3 if p==2 else 1):break
   ts.append(val);sy.append(symbol(val,q[i],p))
  else:
   vals=lambda rs:[[t.numerator,t.denominator] for t in map(F,rs)]
   return [p,prod(sy),dict(x=vals([px])[0],z=vals(zs),tans=vals(ts),sy=sy)]
 raise ValueError(('no local sample',p,d))
print('D',D,file=sys.stderr,flush=True)
data=[]
for name,d, q in [('alphaU',alpha,u),('alphaV',alpha,v),('UV',u,v)]:
 print('tangent',name,file=sys.stderr,flush=True)
 ps=tangent(d)
 print(ps,file=sys.stderr,flush=True)
 rows=[local_qpoint(d,q,ps,p) for p in S]
 out=prod(r[1] for r in rows)
 print(name,out,[(p,r) for p,r,_ in rows],file=sys.stderr,flush=True)
 data.append(dict(name=name,first=d,second=q,tangents=ps,local_rows=rows,total=out))
print(json.dumps(dict(a=a,b=b,D=D,rows=data),indent=2))
