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
a,b=z(-1),z(5)
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
root=[x for x in T if poly(x)==z(0)]
def iso(r,u):
 B0,c0=ad(mu(z(3),pw(r,2)),a),ad(ad(mu(z(5),pw(r,3)),mu(z(3),mu(a,r))),mu(z(2),b))
 aa,bb=su(a,mu(z(5),B0)),su(b,mu(z(7),c0))
 if mu(pw(u,4),aa)!=a or mu(pw(u,6),bb)!=b:return None
 def f(P):
  if P is None or P==(r,z(0)):return None
  x,y=P;den=su(x,r)
  return mu(pw(u,2),ad(x,di(B0,den))),mu(pw(u,3),mu(y,su(z(1),di(B0,pw(den,2)))))
 return f
good=[]
for r in root:
 for u in T[1:]:
  f=iso(r,u)
  if f is None: continue
  assert all(on(f(P)) for P in allP)
  if all(add(add(f(f(P)),neg(f(P))),nt(2,P)) is None for P in allP):
   assert all(add(pi(f(P)),f(pi(P)))==pi(P) for P in allP)
   good.append((r,u))
assert len(good)==2
rr,u=good[0];f=iso(rr,u)
assert good==[((11,3),(5,13)),((11,16),(5,6))]
DATA=dict(eta_options=good,points=400)
