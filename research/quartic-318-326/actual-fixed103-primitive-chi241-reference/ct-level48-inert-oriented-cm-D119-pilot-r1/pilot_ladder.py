import numpy as np
from itertools import product
p=29

class F:
 def __init__(s,m):
  s.m=m;s.q=p**(2*m)
  s.zero=np.zeros((2,m),dtype=np.int64);s.one=s.c(1)
  if m>1:
   a=next((a,b) for a,b in product(range(p),repeat=2)
          if s.basepow((a,b),8 if m==64 else 3)==(1,0)
          and s.basepow((a,b),4 if m==64 else 1)!=(1,0))
   s.d=a
  else:s.d=(0,0)
 def bmul(s,x,y):
  a,b=x;c,d=y;return ((a*c+2*b*d)%p,(a*d+b*c)%p)
 def basepow(s,x,n):
  r=(1,0)
  while n:
   if n&1:r=s.bmul(r,x)
   x=s.bmul(x,x);n//=2
  return r
 def c(s,a,b=0):
  r=s.zero.copy();r[:,0]=(a%p,b%p);return r
 def sc(s,a,n): return (a*n)%p
 def mu(s,x,y):
  a,b=x;c,d=y
  lo=np.convolve(a,c)+2*np.convolve(b,d)
  hi=np.convolve(a,d)+np.convolve(b,c)
  A,B=s.d;m=s.m
  z=lo[m:];w=hi[m:]
  lo[:m-1]+=A*z+2*B*w
  hi[:m-1]+=B*z+A*w
  return np.array([lo[:m]%p,hi[:m]%p])
 def ad(s,a,b):return (a+b)%p
 def su(s,a,b):return (a-b)%p
 def eq(s,a,b):return np.array_equal(a,b)
 def nz(s,a):return bool(np.any(a))
 def pw(s,a,n):
  r=s.one
  while n:
   if n&1:r=s.mu(r,a)
   a=s.mu(a,a);n//=2
  return r
 def inv(s,a):
  assert s.nz(a)
  return s.pw(a,s.q-2)
 def di(s,a,b):return s.mu(a,s.inv(b))
 def sqrt(s,a):
  if not s.nz(a):return s.zero
  if not s.eq(s.pw(a,(s.q-1)//2),s.one):return None
  b=s.q-1;k=0
  while b%2==0:k+=1;b//=2
  if not hasattr(s,'ts'):
   for z in range(100):
    v=s.c(z%29,z//29)
    if s.m>1:v[0,1]=1
    if s.nz(v) and not s.eq(s.pw(v,(s.q-1)//2),s.one):
     s.ts=s.pw(v,b);break
   else:raise ValueError('nonsq')
  c=s.ts;r=s.pw(a,(b+1)//2);t=s.pw(a,b);k0=k
  while not s.eq(t,s.one):
   i=1;x=s.mu(t,t)
   while not s.eq(x,s.one):x=s.mu(x,x);i+=1
   assert i<k0
   v=s.pw(c,1<<(k0-i-1));c=s.mu(v,v);k0=i
   r=s.mu(r,v);t=s.mu(t,c)
  assert s.eq(s.mu(r,r),a)
  return r
 def residue(s,a):
  assert not s.nz(a[:,1:])
  return int(a[0,0]),int(a[1,0])

def jp(P,f):
 return (f.one,f.one,f.zero) if P is None else (*P,f.one)
def jaff(P,f):
 X,Y,Z=P
 if not f.nz(Z):return None
 z=f.inv(Z);z2=f.mu(z,z);return f.mu(X,z2),f.mu(Y,f.mu(z,z2))
def jd(P,f):
 X,Y,Z=P
 if not f.nz(Z) or not f.nz(Y):return jp(None,f)
 m,a,u,s=f.mu,f.ad,f.su,f.sc
 A=m(X,X);B=m(Y,Y);C=m(B,B)
 D=s(u(u(m(a(X,B),a(X,B)),A),C),2);E=s(A,3)
 x=u(m(E,E),s(D,2))
 return x,u(m(E,u(D,x)),s(C,8)),s(m(Y,Z),2)
def ja(P,Q,f):
 X,Y,Z=P;U,V,W=Q
 if not f.nz(Z):return Q
 if not f.nz(W):return P
 m,a,u,s=f.mu,f.ad,f.su,f.sc
 z=m(Z,Z);w=m(W,W)
 x1=m(X,w);x2=m(U,z); y1=m(Y,m(W,w));y2=m(V,m(Z,z))
 h=u(x2,x1);r=u(y2,y1)
 if not f.nz(h):return jd(P,f) if not f.nz(r) else jp(None,f)
 h2=m(h,h);h3=m(h2,h);v=m(x1,h2)
 x=u(u(m(r,r),h3),s(v,2))
 return x,u(m(r,u(v,x)),m(y1,h3)),m(m(Z,W),h)
def jmul(P,k,f):
 r=jp(None,f)
 while k:
  if k&1:r=ja(r,P,f)
  P=jd(P,f);k//=2
 return r

def eig(seed,l,e,f):
 target=l**e
 z=f.c(*ZETA)
 deg=f.m
 cof=abs((-p)**deg-1)//target
 r=0
 for i in range(e):
  m=l**(i+1)
  r=next(r+k*m//l for k in range(l) if ((r+k*m//l)**2-r-k*m//l+30)%m==0)
 for c in range(seed,seed+100):
  x=f.c(c)
  x[0,1]=1
  y=f.sqrt(f.ad(f.pw(x,3),f.one))
  if y is None:continue
  P=jaff(jmul(jp((x,y),f),cof,f),f)
  if P is None:continue
  x,y=P
  I=jp(P,f);rho=jp((f.mu(z,x),y),f);pi=jp((f.pw(x,p),f.pw(y,p)),f)
  Q=jaff(ja(jmul(I,r,f),ja(rho,pi,f),f),f)
  if Q is None:continue
  assert not f.nz(jmul(jp(Q,f),target,f)[2])
  if not f.nz(jmul(jp(Q,f),target//l,f)[2]):continue
  X,Y=Q;J=jp(Q,f);R=jp((f.mu(z,X),Y),f);U=jp((f.pw(X,p),f.pw(Y,p)),f)
  A=jaff(ja(J,ja(R,U,f),f),f)
  B=jaff(jmul(J,r,f),f)
  assert (A is None and B is None) or (A is not None and B is not None and all(f.eq(a,b) for a,b in zip(A,B)))
  return Q,r,c
 raise RuntimeError('no torsion')

# General affine group + Velu for the small number of quotient maps.
def ap(P,Q,A,f):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 u,v,m,a,d,f0=f.su,f.ad,f.mu,f.sc,f.di,f.c
 if f.eq(x,z):
  if not f.nz(v(y,w)):return None
  s=d(v(a(m(x,x),3),A),a(y,2))
 else:s=d(u(w,y),u(z,x))
 r=u(u(m(s,s),x),z)
 return r,u(m(s,u(x,r)),y)
def amul(P,k,A,f):
 O=None
 while k:
  if k&1:O=ap(O,P,A,f)
  P=ap(P,P,A,f);k//=2
 return O

F0=F(1)
ZETA=next((a,b) for a,b in product(range(29),repeat=2)
          if (a,b)!=(1,0) and F0.basepow((a,b),3)==(1,0))
F2=F(64);F3=F(3)

def inbase(P,f):
 return None if P is None else tuple(f.residue(x) for x in P)
def lift(P,f):
 return None if P is None else tuple(f.c(*x) for x in P)

def velu(A,B,K, P, f):
 if P is None:return None
 K=[lift(Q,f) for Q in K]
 if any(all(f.eq(o,q) for o,q in zip(P,Q)) for Q in K):return None
 x,y=P;xo,yo=x,y
 for T in K:
  R=ap(P,T,f.c(*A),f)
  assert R is not None
  xo=f.ad(xo,f.su(R[0],T[0]));yo=f.ad(yo,f.su(R[1],T[1]))
 return xo,yo

def step(A,B,P2,P3,l,k):
 which=F2 if l==2 else F3;Q=P2 if l==2 else P3
 gen=inbase(amul(Q,l**(k-1),which.c(*A),which),which)
 assert gen is not None
 K=[gen]
 if l==3:K.append((gen[0],F0.residue(F0.sc(F0.c(*gen[1]),-1))))
 AA,BB=F0.c(*A),F0.c(*B);AA1,BB1=AA,BB
 for x,y in K:
  X,Y=F0.c(*x),F0.c(*y)
  assert F0.eq(F0.pw(Y,2),F0.ad(F0.ad(F0.pw(X,3),F0.mu(AA,X)),BB))
  tv=F0.ad(F0.sc(F0.pw(X,2),3),AA)
  wv=F0.ad(F0.ad(F0.sc(F0.pw(X,3),5),F0.sc(F0.mu(AA,X),3)),F0.sc(BB,2))
  AA1=F0.su(AA1,F0.sc(tv,5));BB1=F0.su(BB1,F0.sc(wv,7))
 t2=None;t4=None
 if l==2:
  x=F0.c(*gen[0]);a=F0.sc(x,3);b=F0.ad(F0.sc(F0.pw(x,2),3),AA)
  t2=F0.residue(F0.di(F0.sc(b,256),F0.su(F0.pw(a,2),F0.sc(b,4))))
  if k>=2:
   R=amul(P2,2**(k-2),F2.c(*A),F2)
   u=F0.su(F0.c(*F2.residue(R[0])),x)
   assert F0.eq(F0.pw(u,2),b)
   t4=F0.residue(F0.di(F0.sc(u,64),F0.su(a,F0.sc(u,2))))
 R2=velu(A,B,K,P2,F2);R3=velu(A,B,K,P3,F3)
 a,b=F0.residue(AA1),F0.residue(BB1)
 for R,f in ((R2,F2),(R3,F3)):
  if R is not None:
   x,y=R
   assert f.eq(f.pw(y,2),f.ad(f.ad(f.pw(x,3),f.mu(f.c(*a),x)),f.c(*b)))
 return (a,b,R2,R3),(t2,t4)

def genp():
 P2,r2,c2=eig(0,2,8,F2);P3,r3,c3=eig(0,3,2,F3)
 return ( (0,0),(1,0),P2,P3 ),r2,r3,c2,c3

