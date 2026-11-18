"""Halve both marked rational points and add in Q(sqrt(17),sqrt(409)); verify trace, antitrace, global norm marks."""
from fractions import Fraction as F
from math import isqrt,prod
import json
B,D=17,409
class K:
 def __init__(s,*v):s.v=tuple(v[0].v) if len(v)==1 and isinstance(v[0],K) else tuple(map(F,v))+tuple(F(0) for _ in range(4-len(v)))
 def __add__(s,o):return K(*(x+y for x,y in zip(s.v,K(o).v)))
 __radd__=__add__
 def __neg__(s):return K(*(-x for x in s.v))
 def __sub__(s,o):return s+-K(o)
 def __rsub__(s,o):return K(o)+-s
 def __mul__(s,o):
  a=[0]*4
  for i,x in enumerate(s.v):
   for j,y in enumerate(K(o).v):a[i^j]+=x*y*(B if i&j&1 else 1)*(D if i&j&2 else 1)
  return K(*a)
 __rmul__=__mul__
 def conj(s,i):return K(*(x*(-1 if j&i else 1) for j,x in enumerate(s.v)))
 def __truediv__(s,o):
  o=K(o);p=o.conj(1)*o.conj(2)*o.conj(1).conj(2);a,b,c,d=(p*o).v;assert (b,c,d)==(0,0,0) and a
  return K(*(f/a for f in (s*p).v))
 def __rtruediv__(s,o):return K(o)/s
 def __pow__(s,k):return prod([s]*k,start=K(1))
 def __eq__(s,o):return s.v==K(o).v
def affine_add(P,Q,n):
 x,y=P;u,v=Q
 if x==u and y==-v:return None
 t=(3*x*x+4*n*x-3*n*n)/(2*y) if x==u else (v-y)/(u-x)
 w=t*t-2*n-x-u
 return w,t*(x-w)-y
def on(P,n):
 x,y=P;return y*y==x*(x-n)*(x+3*n)
def half(uvw,N,n):
 w=K(0,1);t=K(0,0,1) if N!=n else 1
 u,v,z=uvw;r=[u*w/t,v/t,-z*w/t];x=r[0]**2;y=-prod(r);u=x+r[0]*r[1]+r[1]*r[2]+r[2]*r[0];v=-y-sum(r)*(u-x)
 assert on((u,v),n) and affine_add((u,v),(u,v),n)==(x,y)
 return (u,v),(x,y)
n=323
def den(*v):return [F(x,v[-1]) for x in v[:-1]]
A,S=half(den(23297,85425,29719,2444),n,n);V,T=half(den(134500798043,482802274515,176711378011,750654112),n*D,n)
P=affine_add(A,V,n);assert P and on(P,n)
assert all(x.v[1]==x.v[3]==0 for x in P);sigma=lambda pt:tuple(z.conj(2) for z in pt)
Ps=sigma(P);assert affine_add(P,Ps,n)==S and affine_add(P,(Ps[0],-Ps[1]),n)==T
X=P[0]/n; a,_,z,_=X.v;assert z
f=lambda X:X*(X-1)*(X+3)
norms=[(a-i)**2-D*z*z for i in [0,1,-3]]
def sqrt(x):
 assert x>0 and (i:=isqrt(x.numerator))**2==x.numerator and (j:=isqrt(x.denominator))**2==x.denominator;return F(i,j)
u,v,w=[sqrt(q/s) for q,s in zip(norms,[B,1,B])]
assert B*(w*w-4*u*u)+3*v*v==12 and 4*D*z*z==(B*u*u+1-v*v)**2-4*B*u*u
# Directly recover the rational n from X alone, not from the original n.
Z=f(X);r=sqrt(norms[0]*norms[1]*norms[2]);d0=2*(Z.v[0]+r)
if d0==0:r=-r;d0=2*(Z.v[0]+r)
assert d0 and (Z+r)**2==d0*Z
ratio=F(d0/n)
assert ratio>0 and (isqrt(ratio.numerator)**2==ratio.numerator and isqrt(ratio.denominator)**2==ratio.denominator or (lambda s:isqrt(s.numerator)**2==s.numerator and isqrt(s.denominator)**2==s.denominator)(ratio/D))
print(json.dumps({k:str(x) for k,x in dict(beta=B,theta=D,n=n,a=a,z=z,u=u,v=v,w=w,n_recovered=d0).items()},indent=2))
