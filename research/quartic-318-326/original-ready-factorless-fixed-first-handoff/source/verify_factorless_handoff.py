from fractions import Fraction as F
from math import gcd
import json

# Exact two-variable polynomial checks over Z[N,D].
def h(k):return {(0,0):k} if k else {}
N={(1,0):1};D={(0,1):1}
def a(*vals):
 out={}
 for x in vals:
  for i,v in x.items():out[i]=out.get(i,0)+v
 return {i:v for i,v in out.items() if v}
def s(n,x):return {i:n*v for i,v in x.items() if n*v}
def m(x,y):
 out={}
 for (i,j),v in x.items():
  for (k,l),w in y.items():
   t=(i+k,j+l);out[t]=out.get(t,0)+v*w
 return {i:v for i,v in out.items() if v}
def power(x,n):
 out=h(1)
 for _ in range(n):out=m(out,x)
 return out
C=s(10000,D);An=a(C,s(3,N));J=m(a(C,s(-1,N)),a(C,s(-9,N)))
assert a(power(An,2),s(-1,J))==s(16,m(C,N))
assert a(power(An,2),s(3,J))==s(4,power(a(C,s(-3,N)),2))
L=m(a(s(289,D),s(-1,N)),J)
M=s(289,m(D,power(An,2)))
def ev(p,n,d):return sum(v*n**i*d**j for (i,j),v in p.items())

def v_p(r,p):
 v=0
 a,b=r.numerator,r.denominator
 assert a
 while a%p==0:a//=p;v+=1
 while b%p==0:b//=p;v-=1
 return v

def raw(b,rD):
 B=17*b;u=B/10000;A=1+3*u;T=B*(1-u)*(1-9*u)/A**2
 y=8*B**2*(1-3*u)/(100*A**2)
 delta=1-B/289
 assert 0<b<17 and 0<T<B and y
 assert B-T==(4*B/(100*A))**2
 assert B+3*T==B*(2*(1-3*u)/A)**2
 assert y*y==B*(B-T)*(B+3*T)
 n,d=B.numerator*rD,B.denominator*rD
 ell=F(ev(L,n,d),ev(M,n,d))
 assert ell==delta*T/B
 return B,T,y,delta,n,d,ell

# Check the d-multiplier simplification on exact rational controls only,
# not on a simulated prime tuple or a manufactured physical source.
roots=[F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
from math import prod
u,q=7907,101;Clr=2*407*2399;Q=15;sf=F(-3,5)
bind=[]
for c in [F(1),F(-1,5),F(1,7)]:
 t=F(u,Clr**2*Q**2*q);T=c*c*t
 rr=[F(u)-Clr**2*r*Q**2*q/(c*c) for r in roots]
 assert all(x.denominator==1 for x in rr)
 d=q*prod(rr)
 r=c**5*sf/((Clr*Q)**5*q**3)
 b=prod(T-r0 for r0 in roots)*sf**2
 assert b==d*r*r
 bind.append([str(c),len(rr),b==d*r*r])

# One nonoriginal square-complement Ready control for the complete raw map.
v=F(805,1009);b=17*(1-v*v)
assert [v_p(b,p) for p in (2,3,17)]==[3,1,2]
B,T,y1,delta,n,d,ell=raw(b,9)
w=delta*y1/B
assert delta==v*v
assert w*w==B*(v*v-ell)*(v*v+3*ell)
s= B*v; y2=B**4*v*w
D2=T*B*B*delta; X=B*s*s
assert s and y2*y2==X*(X-D2)*(X+3*D2)
Z=prod([v.denominator,w.denominator]); x=v*Z; W=w*Z*Z
eL,eM=ev(L,n,d),ev(M,n,d)
assert x.denominator==W.denominator==1
assert d*eM**2*W**2==n*(eM*x*x-eL*Z*Z)*(eM*x*x+3*eL*Z*Z)
assert gcd(n,d)>1
print(json.dumps(dict(detector_product_controls=bind,
    local_depths_control=[v_p(b,p) for p in (2,3,17)], scalar_control=str(b),
    positive_and_nonzero=True, unreduced_denominator_control=True,
    first_ordinate=str(y1), second_ordinate=str(y2),
    scope='Symbolic identities and one nonoriginal square-complement control; no literal detector or scalar companion rational point.'),
    indent=2,sort_keys=True))
