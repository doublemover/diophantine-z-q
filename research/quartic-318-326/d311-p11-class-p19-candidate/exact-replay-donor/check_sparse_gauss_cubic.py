#!/usr/bin/env python3
"""Reduce oriented ideal factors with scalar cubic data, without expanding the exponents."""
from math import gcd,isqrt
from functools import reduce
from itertools import product
import json
p=29

def mul(a,b):return ((a[0]*b[0]+2*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def pw(a,n):
 if n<0:return pw(pw(a,p*p-2),-n)
 t=(1,0)
 while n:
  if n&1:t=mul(t,a)
  a=mul(a,a);n//=2
 return t
def add(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def exgcd(a,b):
 if b==0:return abs(a),1 if a>=0 else -1,0
 d,s,t=exgcd(b,a%b)
 return d,t,s-a//b*t

def hnf(xs):
 A,B=0,0
 for a,b in xs:
  v,s,t=exgcd(B,b);A,B=s*A+t*a,v
 assert B>0
 H=gcd(*[a-A*(b//B) for a,b in xs]); assert H>0
 return ((H,0),(A%H,B))

class Quad:
 def __init__(self,D,rt):
  assert D<0 and D%4 in (0,1) and pw(rt,2)==(D%p,0) and rt[1]
  self.D=D;self.t=D%2;self.c=(self.t*self.t-D)//4
  self.om=tuple(x*pow(2,-1,p)%p for x in add((self.t,0),rt))
  self.unit=((1,0),(0,1))
 def mul(self,x,y):
  a,b=x;c,d=y
  return a*c-self.c*b*d,a*d+b*c+self.t*b*d
 def conj(self,z):
  a,b=z;return a+self.t*b,-b
 def N(self,z):
  a,b=z;return a*a+self.t*a*b+self.c*b*b
 def dot2(self,x,y):
  a,b=x;c,d=y
  return 2*a*c+self.t*(a*d+b*c)+2*self.c*b*d
 def gauss(self,x,y):
  while True:
   if self.N(y)<self.N(x):x,y=y,x
   # k = floor(dot(x,y)/norm(x)+1/2), exact on signed integers.
   L=self.N(x);k=(self.dot2(x,y)+L)//(2*L)
   if k==0:
    assert 2*abs(self.dot2(x,y))<=2*L and self.N(x)<=self.N(y)
    return x,y
   y=(y[0]-k*x[0],y[1]-k*x[1])
 def red(self,z):
  return add((z[0]%p,0),mul((z[1]%p,0),self.om))
 def reduce(self,I):
  I=hnf(I)
  assert I[0][0]*I[1][1]%p
  u,v=self.gauss(*I);Q=self.N(u);assert Q%p and self.red(u)!=(0,0)
  a,b=self.mul(v,self.conj(u));g=gcd(a,b,Q);d=Q//g
  assert d%p
  R=hnf(((d,0),(a//g,b//g)))
  assert R[0]==(d,0) and R[1][1]==1 and 3*d*d<=-self.D
  assert hnf([self.mul(u,z) for z in R])==hnf([(d*a,d*b) for a,b in I])
  return R,pw(mul(self.red(u),(pow(d,-1,p),0)),280)
 def rawmul(self,I,J):return hnf([self.mul(u,v) for u in I for v in J])
 def mulstate(self,X,Y):
  J,c=self.reduce(self.rawmul(X[0],Y[0]));return J,mul(mul(X[1],Y[1]),c)
 def factorstate(self,l,r,e):
  # r is the named residue of omega at the first split prime.
  assert l!=p and (r*r-self.t*r+self.c)%l==0 and (2*r-self.t)%l!=0
  I=((l,0),((-r)%l,1))
  if e<0:I=hnf(list(map(self.conj,I)));e=-e # discard the rational l^-e: cubic class trivial
  J=self.reduce(I);A=(self.unit,(1,0));k=0
  while e:
   if e&1:A=self.mulstate(A,J);k+=1
   e//=2
   if e:J=self.mulstate(J,J);k+=1
  return A,k

def normprod(x):
 z=(1,0)
 for a in x:z=mul(z,a)
 return z
D=-421991;K=Quad(D,(0,9));omega=(0,1)
P=((2,0),omega)
assert K.reduce(P)[0]!=K.unit
A,k=K.factorstate(2,0,167);assert A==(K.unit,(14,24))
P0=K.unit
for _ in range(167):P0=K.rawmul(P0,P)
B=K.reduce(P0);g=K.gauss(*P0)[0]
assert B==A and K.N(g)==2**167
Bign=167*(10**100+22);B,kk=K.factorstate(2,0,Bign);assert B==(K.unit,(14,5))
C,nki=K.factorstate(2,0,-Bign);assert C==(K.unit,(14,24)) and K.mulstate(B,C)==(K.unit,(1,0))
assert {u for u in range(1,p) if pw((u,0),280)!=(1,0)}==set()
# Same norm-to-M local cubic can hide the named orientation in E.
F=[(a,b) for a,b in product((1,-1),repeat=2)]
w=(0,9);laws=[]
for a,b in F:
 b1=(a*11+11)*(b*8+8);b2=-(a*11-11)*(b*8+8)
 def rat(k):return mul(add((1,0),mul((k%p,0),w)),pw(add((1,0),mul((-k%p,0),w)),-1))
 laws.append([rat(b1),rat(b2)])
rows=list(zip(*laws)); assert rows[0][0]==rows[1][2]==(22,16) and rows[1][0]==(1,0)
assert normprod(rows[0])==normprod(rows[1]); assert pw(rows[0][0],280)!=(1,0)
chi=[[a**u*b**v for a,b in F] for u,v in product((0,1),repeat=2)]
N=[[pw(normprod([pw(z,sg) for z,sg in zip(row,C)]),280) for C in chi] for row in rows]
assert [normprod(row) for row in N]==[pw(row[0],280) for row in rows]
print(json.dumps(dict(scope='constructed fixed-reference-field oriented-ideal regressions; not an actual CM ratio or moving exponent',
 discriminant=D,prime_orientation='(2,omega)',prime_class_order=167,raw_primitive_vector=g,
 exponent_167=dict(multiplications=k,cubic=A[1]),large_exponent=dict(exponent=str(Bign),multiplications=kk,cubic=B[1],inverse_multiplications=nki,inverse_cubic=C[1]),
 named_norm_to_M_agrees=normprod(rows[0]),named_first_place_differs=[r[0] for r in rows],four_cubic_projections=N),sort_keys=True,separators=(',',':')))
