from itertools import product
from math import gcd,isqrt
import json,sys
import flint
p=19
F=flint.fq_default_ctx(modulus=flint.fmpz_mod_poly_ctx(p)([-2,0,1]),var='s')
s=F.gen();ii=3*s
C=flint.fq_default_poly_ctx(F)
x=C.gen();one=C([1]);zero=C([0])
els=[F(a)+b*s for a,b in product(range(p),repeat=2)]
print('starting exact selected 2-cycle',file=sys.stderr)
def fcoords(q):return next([a,b] for a,b in product(range(p),repeat=2) if q==F(a)+b*s)
class R:
 def __init__(self,x,y=one):
  if isinstance(x,R):
   assert y==one
   self.x=x.x;self.y=x.y;return
  x=x if isinstance(x,type(one)) else C([x])
  y=y if isinstance(y,type(one)) else C([y])
  assert y
  g=x.gcd(y)
  x=x//g;y=y//g
  c=y.leading_coefficient()
  self.x=x/c;self.y=y/c
 def __add__(self,v):
  v=R(v);return R(self.x*v.y+v.x*self.y,self.y*v.y)
 __radd__=__add__
 def __neg__(self):return R(-self.x,self.y)
 def __sub__(self,v):return self+-R(v)
 def __rsub__(self,v):return R(v)-self
 def __mul__(self,v):
  v=R(v);return R(self.x*v.x,self.y*v.y)
 __rmul__=__mul__
 def __truediv__(self,v):
  v=R(v);return R(self.x*v.y,self.y*v.x)
 def __rtruediv__(self,v):return R(v)/self
 def __eq__(self,v):
  v=R(v);return (self.x,self.y)==(v.x,v.y)
 def __pow__(self,n):return R(self.x**n,self.y**n)
 def d(self):return R(self.x.derivative()*self.y-self.x*self.y.derivative(),self.y**2)
 def sub(self,q):return R(self.x.compose(q),self.y.compose(q))
 def deg(self):return max(self.x.degree(),self.y.degree())
xx=R(x);f=xx**3-xx
def add0(P,Q):
 if P is None:return Q
 if Q is None:return P
 X,Y=P;U,V=Q
 if X==U:
  if Y==-V:return None
  assert Y==V
  m=(3*X**2-1)/(2*f*Y)
 else:m=(V-Y)/(U-X)
 a=f*m**2-X-U
 return a,m*(X-a)-Y
def mul0(n,P):
 if n<0:return mul0(-n,(P[0],-P[1])) if P else None
 Q=None
 while n:
  if n&1:Q=add0(Q,P)
  n//=2
  if n:P=add0(P,P)
 return Q
# Norm-5 eta: exact pi=-1 E[5] line, normalized scale2.
def ad(A,B):
 if A is None:return B
 if B is None:return A
 x,y=A;u,v=B
 if x==u:
  if y+v==0:return None
  assert y==v
  k=(3*x*x-1)/(2*y)
 else:k=(v-y)/(u-x)
 r=k*k-x-u
 return r,k*(x-r)-y
def m0(k,P):
 Q=None
 while k:
  if k&1:Q=ad(Q,P)
  k//=2
  if k:P=ad(P,P)
 return Q
els5=[]
for a,b in product(els,repeat=2):
 if b==0 or b*b!=a**3-a or a**19!=a or b**19!=-b:continue
 if m0(5,(a,b)) is None:els5.append((a,b))
assert len(els5)==4
Kx={x for x,y in els5}
assert len(Kx)==2
A3=-1-10*sum(3*k*k-1 for k in Kx);B3=-14*sum(5*k**3-3*k for k in Kx)
assert 16*A3==-F(1) and B3==0
etaX=xx
for k in Kx:etaX+=-2*xx-4*k+2*(f+(k**3-k))/(xx-k)**2
etaY=etaX.d()
eta=(4*etaX,8*etaY)
P=(xx,R(1))
frP=(xx**19,f**9)
assert add0(eta,eta)==add0(P,frP)
iEta=(-eta[0],eta[1]*ii)
iP=(-xx,R(ii))
Al=add0(add0(add0((xx,-R(1)),mul0(3,iP)),mul0(3,eta)),mul0(2,iEta))
assert Al is not None and Al[0].deg()==78
A=-F(1);B=F(0);rho=Al[0];ks=[]
def ve(A,B,k):
 return A-5*(3*k*k+A),B-7*(5*k**3+3*A*k+2*B)
def rem(P,b):
 # basis 1,u in relation u^2 = x*u-b
 v=zero;w=zero
 for k in range(P.degree(),-1,-1):
  v,w=C([P[k]])-b*w,v+x*w
 return v,w
for step in range(19):
 k0=[k for k in els if k**3+A*k+B==0 and rho.y(k)==0]
 assert len(k0)==1
 k=k0[0];ks.append(k)
 b=3*k*k+A
 r=rho.sub(x+k)-k
 z=r+b/r
 a0,a1=rem(z.x,b);b0,b1=rem(z.y,b)
 assert a0*b1==a1*b0
 nz=R(a0,b0) if b0 else R(a1,b1)
 rho=nz.sub(x-k)+k
 assert rho.deg()==78
 A,B=ve(A,B,k)
 # For the selected α degree this cycle is separable away 2,3,13.
 assert 4*A**3+27*B**2!=F(0)
assert B==0
mu=(1341-31*5*s)/2
assert mu!=mu**19
sv=[u for u in els if u and u**4*A==-F(1) and R(1)/R(u)==R(mu) and Al[0].sub(x*u*u)==rho*u*u]
assert len(sv)==1
u=sv[0]
n=311
forms=[]
for a in range(1,isqrt(n//3)+1):
 for b in range(-a,a+1):
  if (b*b+n)%(4*a):continue
  c=(b*b+n)//(4*a)
  if a>c or (a==c or abs(b)==a) and b<0 or gcd(a,gcd(b,c))!=1:continue
  forms.append([a,b,c])
assert len(forms)==19 and not any(a*a+n*b*b==8 for a in range(-3,4) for b in (-1,0,1))
assert 1341**2+311*31**2==4*2**19
print('19 exact horizontal arrows',list(map(fcoords,ks)),'closing scale',fcoords(u),'mu',fcoords(mu),file=sys.stderr)
# In Z/19^K[s]/(s^2-2), lift the named short Weierstrass
# branch B=T along the exact 19 kernels and solve closure.
K=8;M=p**K
z=(0,0);o=(1,0)
def B0(a):return (a%M,0)
def plus(a,b):return (a[0]+b[0])%M,(a[1]+b[1])%M
def neg(a):return -a[0]%M,-a[1]%M
def minus(a,b):return plus(a,neg(b))
def mul(a,b):return (a[0]*b[0]+2*a[1]*b[1])%M,(a[0]*b[1]+a[1]*b[0])%M
def sc(a,b):return a*b[0]%M,a*b[1]%M
def pw(a,k):
 r=o
 while k:
  if k&1:r=mul(r,a)
  a=mul(a,a);k//=2
 return r
def inv(a):
 d=pow((a[0]*a[0]-2*a[1]*a[1])%M,-1,M)
 return a[0]*d%M,-a[1]*d%M
def lift(t,fun):
 for j in range(K.bit_length()+1):
  f,d=fun(t)
  if f==z:return t
  t=minus(t,mul(f,inv(d)))
 assert fun(t)[0]==z
 return t
def close(T,ret=False):
 A,B=B0(-1),T;arr=[]
 for k0 in ks:
  k=lift(tuple(fcoords(k0)),lambda x:(plus(plus(pw(x,3),mul(A,x)),B),plus(sc(3,pw(x,2)),A)))
  arr.append((A,B,k))
  A,B=minus(A,sc(5,plus(sc(3,pw(k,2)),A))),minus(B,sc(7,plus(plus(sc(5,pw(k,3)),sc(3,mul(A,k))),sc(2,B))))
 s0=lift(tuple(fcoords(u)),lambda x:(plus(mul(A,pw(x,4)),o),sc(4,mul(A,pw(x,3)))))
 b=mul(B,pw(s0,6))
 return (arr,s0) if ret else minus(b,T)
f0=close(z);f1=close(B0(p))
print('closure at 0 mod361',[u%(p*p) for u in f0],file=sys.stderr)
assert all(a%p==0 for a in f0+f1)
d0=tuple((a-b)//p%p for a,b in zip(f1,f0))
assert d0!=(0,0)
D=(mu/mu**19-F(1))
print('certified closure derivative',d0,'CM derivative prediction',fcoords(D),file=sys.stderr)
assert tuple(fcoords(D))==d0
T=z
for k in range(1,K):
 t=close(T)
 assert all(a%p**k==0 for a in t)
 err=mul(tuple(a//p**k%p for a in t),inv(d0))
 T=minus(T,sc(p**k,tuple(a%p for a in err)))
assert close(T)==z
print('exact lifted short B mod 19^8',T,'B mod 19^5',[a%p**5 for a in T],file=sys.stderr)
arr,s0=close(T,ret=True)
data={'prime':19,'precision':K,'D':-311,'source_model':[-1,T],'ordered_alpha':[2,0],
 'ordered_vertical_root_mod19':[0,5],'fixed_quadratic_place_s_squared':2,'horizontal_cycle':[[fcoords(k),A,B,pp] for k,(A,B,pp) in zip(ks,arr)],
 'closing_scale_mod19':fcoords(u),'closing_scale':s0,'closure_derivative_mod19':d0,'scoped':'fixed control; not a full p11 valuation or original detector'}
print(json.dumps(data,indent=2,sort_keys=True))
