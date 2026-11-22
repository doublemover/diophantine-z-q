from itertools import product
from functools import lru_cache
from random import Random
p=19
q=p**6
F=list(product(range(p),repeat=2)); z=lambda n:(n%p,0)
def a(x,y):return ((x[0]+y[0])%p,(x[1]+y[1])%p)
def n(x):return ((-x[0])%p,(-x[1])%p)
def s(x,y):return a(x,n(y))
def m(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def pw(x,k):
 v=z(1)
 while k:
  if k&1:v=m(v,x)
  x=m(x,x);k//=2
 return v
def d(x,y):
 assert y!=z(0)
 return m(x,pw(y,359))
tcoef=next(x for x in F if pw(x,9)==z(1) and pw(x,3)!=z(1))
zero=(z(0),)*3;one=(z(1),)+(z(0),)*2
def E(*x):return (tuple(x),)+(z(0),)*2
c=lambda k:E(*z(k))
def base(x):
 assert x[1:]==zero[1:]
 return x[0]
def A(x,y):return tuple(a(u,v) for u,v in zip(x,y))
def N(x):return tuple(n(u) for u in x)
def S(x,y):return A(x,N(y))
def M(x,y):
 v=[z(0)]*5
 for i in range(3):
  if x[i]==z(0):continue
  for j in range(3):
   if y[j]==z(0):continue
   v[i+j]=a(v[i+j],m(x[i],y[j]))
 for j in range(3,5):
  v[j-3]=a(v[j-3],m(tcoef,v[j]))
 return tuple(v[:3])
def P(x,k):
 v=one
 while k:
  if k&1:v=M(v,x)
  x=M(x,x);k//=2
 return v
@lru_cache(20000)
def I(x):
 assert x!=zero
 return P(x,q-2)
def D(x,y):return M(x,I(y))
def sqr(x):return M(x,x)
def sqrt(x):
 if x==zero:return zero
 if P(x,(q-1)//2)!=one:return None
 odd=q-1;e=0
 while odd%2==0:odd//=2;e+=1
 z0=E(*next(k for k in F if pw(k,180)==z(-1)))
 assert P(z0,(q-1)//2)==N(one)
 v=P(z0,odd);y=P(x,(odd+1)//2);t=P(x,odd)
 while t!=one:
  i=1;t0=sqr(t)
  while t0!=one:i+=1;t0=sqr(t0)
  assert i<e
  h=P(v,2**(e-i-1));v=sqr(h);y=M(y,h);t=M(t,v);e=i
 assert sqr(y)==x
 return y

L0=c(-1);B0=c(5)
def add(P,Q,L=L0,a2=zero):
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u and A(y,v)==zero:return None
 if x==u:
  h=D(A(A(M(c(3),sqr(x)),M(M(c(2),a2),x)),L),M(c(2),y))
 else:h=D(S(v,y),S(u,x))
 r=S(S(S(sqr(h),a2),x),u)
 return r,S(M(h,S(x,r)),y)
def ng(P):return None if P is None else (P[0],N(P[1]))
def mu(k,P,L=L0,a2=zero):
 if k<0:return mu(-k,ng(P),L,a2)
 Q=None
 while k:
  if k&1:Q=add(Q,P,L,a2)
  P=add(P,P,L,a2);k//=2
 return Q
def on(P,L=L0,B=B0,a2=zero):
 if P is None:return True
 x,y=P
 return sqr(y)==A(A(A(PW(x,3),M(a2,sqr(x))),M(L,x)),B)
PW=P
def velu(L,B,K):
 R,T=L,B
 for x,_ in K:
  h=A(M(c(3),sqr(x)),L)
  v=A(A(M(c(5),PW(x,3)),M(c(3),M(L,x))),M(c(2),B))
  R=S(R,M(c(5),h));T=S(T,M(c(7),v))
 def f(P):
  if P is None or P in K:return None
  x,y=P
  for U in K:
   V=add(P,U,L)
   assert V is not None
   x=A(x,S(V[0],U[0]));y=A(y,S(V[1],U[1]))
  assert on((x,y),R,T)
  return x,y
 return R,T,f

rng=Random(4819)
def basis(l,k):
 b=[];n0=l**k
 for K in range(128):
  x=tuple((rng.randrange(p),rng.randrange(p)) for _ in range(3))
  y=sqrt(A(A(PW(x,3),M(L0,x)),B0))
  if y is None:continue
  U=mu((p**3+1)//n0,(x,y))
  V=mu(n0//l,U)
  if V is None or b and V in [mu(a,mu(n0//l,b[0])) for a in range(l)]:continue
  assert mu(n0,U) is None
  b.append(U)
  if len(b)==2:return b
 raise ValueError("torsion basis not found")
def reps(l,k):
 n0=l**k;A,B=basis(l,k)
 u=[mu(i,A) for i in range(n0)];v=[mu(i,B) for i in range(n0)]
 allT=[add(a0,b0) for a0 in u for b0 in v]
 assert len(set(allT))==n0**2
 seen=set();R=[]
 for T in allT:
  if T in seen or mu(n0//l,T) is None:continue
  seen.update(mu(k0,T) for k0 in range(n0) if k0%l)
  R.append(T)
 return R

def pi(P):return None if P is None else tuple(PW(u,p) for u in P)
rr=E(11,3);uu=E(5,13);t=A(M(c(3),sqr(rr)),L0)
def eta(P):
 if P is None or P==(rr,zero):return None
 x,y=P;h=S(x,rr)
 Q=M(PW(uu,2),A(x,D(t,h))),M(PW(uu,3),M(y,S(one,D(t,sqr(h)))))
 assert on(Q)
 return Q
P7,Q7=basis(7,1)
M7={add(mu(t,P7),mu(s,Q7)):(t,s) for t,s in product(range(7),repeat=2)}
assert len(M7)==49
def lab(R):return [M7[u] for u in [R,eta(R),pi(R),eta(pi(R))]]
m1,m2=lab(P7),lab(Q7)
ker=[k for k in product(range(7),repeat=4) if all(sum(k[j]*mat[j][i] for j in range(4))%7==0 for mat in (m1,m2) for i in range(2))]
assert len(ker)==7
assert (1,5,5,4) in ker
assert tcoef==(4,0) and pw(tcoef,9)==z(1) and pw(tcoef,3)!=z(1)
assert pow(361,3,27)==1 and pow(361,1,27)!=1
DATA=dict(tcoef=tcoef,P7=P7,Q7=Q7,ker=ker,matrices=[m1,m2])
