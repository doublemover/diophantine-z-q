from itertools import product
from collections import Counter
import json
p=7
F=list(product(range(p),repeat=2)); z=lambda x:(x%p,0)
def a(x,y):return ((x[0]+y[0])%p,(x[1]+y[1])%p)
def n(x):return ((-x[0])%p,(-x[1])%p)
def s(x,y):return a(x,n(y))
def m(x,y):return ((x[0]*y[0]-x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def pp(x,k):
 v=z(1)
 while k:
  if k&1:v=m(v,x)
  x=m(x,x);k//=2
 return v
def d(x,y):
 assert y!=z(0)
 return m(x,pp(y,47))
def j(t):
 for a0 in (2,4,16):
  if a(t,z(a0))==z(0):return None
  t=d(m(t,t),a(t,z(a0)))
 return None if t==z(0) else d(pp(a(t,z(256)),3),m(t,t))
def phi(X,Y):
 t=s(X,d(z(1),X));w=d(Y,m(X,X));x=d(a(a(w,m(t,t)),z(2)),z(2))
 return x,m(t,x)
def on(P):
 if P is None:return True
 x,y=P
 return m(y,y)==m(m(x,a(x,z(1))),s(x,z(3)))
def neg(P):return None if P is None else (P[0],n(P[1]))
def gp(P,Q):
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u and a(y,v)==z(0):return None
 h=d(s(s(m(z(3),m(x,x)),m(z(4),x)),z(3)),m(z(2),y)) if x==u else d(s(v,y),s(u,x))
 r=s(s(a(m(h,h),z(2)),x),u)
 R=r,s(m(h,s(x,r)),y)
 assert on(R)
 return R
count=Counter()
for X in F:
 if X==z(0):continue
 X4=pp(X,4)
 for Y in F:
  if m(Y,Y)!=a(a(m(X4,X4),m(z(14),X4)),z(1)):continue
  W=d(a(a(Y,X4),z(1)),z(2))
  if W==z(0):continue
  H=a(s(X,z(2)),d(m(z(3),X),W))
  if j(H)!=z(1728):continue
  P=phi(X,Y)
  assert on(P)
  J=gp(P,neg(tuple(pp(u,7) for u in P)))
  assert gp(J,J)==(z(-1),z(0))
  count[J]+=1
assert dict(count)=={(z(1),(0,2)):16,(z(1),(0,5)):16,(z(4),(0,1)):8,(z(4),(0,6)):8}
assert (1**2+3**2)%7==3 and pow(3,3,7)==6
print(json.dumps(dict(scope="original linear-q inert seven zero finite bit; not rank",
                      finite_pair=(z(-1),z(0)),labels=sum(count.values()),phases=sorted(count.items()),
                      gaussian_norm_mod7=3),indent=2,sort_keys=True))
