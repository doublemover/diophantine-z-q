from itertools import product
p=19
T=list(product(range(p),repeat=2))
def z(a,b=0):return (a%p,b%p)
def ad(a,b):return z(a[0]+b[0],a[1]+b[1])
def ng(a):return z(-a[0],-a[1])
def su(a,b):return ad(a,ng(b))
def mu(a,b):return z(a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def pw(a,k):
 b=z(1)
 while k:
  if k&1:b=mu(a,b)
  a=mu(a,a);k//=2
 return b
def di(a,b):assert b!=z(0);return mu(a,pw(b,359))
a,b=z(-1),z(0)
def poly(x):return ad(ad(pw(x,3),mu(a,x)),b)
def on(P):return P is None or mu(P[1],P[1])==poly(P[0])
def add(P,Q):
 if P is None:return Q
 if Q is None:return P
 x,y=P;X,Y=Q
 if x==X and ad(y,Y)==z(0):return None
 t=di(ad(mu(z(3),pw(x,2)),a),mu(z(2),y)) if x==X else di(su(Y,y),su(X,x))
 r=su(su(pw(t,2),x),X)
 return r,su(mu(t,su(x,r)),y)
def neg(P):return None if P is None else(P[0],ng(P[1]))
def nt(n,P):
 if n<0:return nt(-n,neg(P))
 Q=None
 while n:
  if n&1:Q=add(Q,P)
  P=add(P,P);n//=2
 return Q
def pi(P):return None if P is None else tuple(pw(x,19) for x in P)
allP=[None]+[(x,y) for x in T for y in T if pw(y,2)==poly(x)]
assert len(allP)==400 and sum(pi(P)==P for P in allP)==20

ks=[P for P in allP if P is not None and nt(5,P) is None and add(P,pi(P)) is None]
assert len(ks)==4
A1,B1=a,b
for x,y in ks:
 t=ad(mu(z(3),pw(x,2)),a)
 w=ad(ad(mu(z(5),pw(x,3)),mu(z(3),mu(a,x))),mu(z(2),b))
 A1=su(A1,mu(z(5),t));B1=su(B1,mu(z(7),w))
assert mu(pw(z(2),4),A1)==a and mu(pw(z(2),6),B1)==b
def f(P):
 if P is None or P in ks:return None
 x,y=P;xx,yy=x,y
 for U in ks:
  V=add(P,U);assert V is not None
  xx=ad(xx,su(V[0],U[0])); yy=ad(yy,su(V[1],U[1]))
 return mu(pw(z(2),2),xx),mu(pw(z(2),3),yy)
assert all(on(f(P)) and nt(2,f(P))==add(P,pi(P)) for P in allP)
assert ks==[((13,0),(0,3)),((13,0),(0,16)),((14,0),(0,4)),((14,0),(0,15))]
DATA=dict(kernel=ks,normalized_quotient=[A1,B1],points=400)
