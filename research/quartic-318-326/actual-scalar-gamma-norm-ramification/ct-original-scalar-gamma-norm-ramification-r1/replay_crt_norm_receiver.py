#!/usr/bin/env python3
from fractions import Fraction as F
from functools import reduce
from math import gcd,isqrt
import json

# Ring Z[(1+sqrt(5))/2], coordinate law and norm-Euclidean algorithm.
def add(x,y):return x[0]+y[0],x[1]+y[1]
def sub(x,y):return x[0]-y[0],x[1]-y[1]
def mul(x,y):
 a,b=x;c,d=y
 return a*c+b*d,a*d+b*c+b*d
def co(x):return x[0]+x[1],-x[1]
def norm(x):
 a,b=mul(x,co(x));assert b==0
 return a
def euclid(a,b):
 steps=0
 while b!=(0,0):
  q=tuple(round(F(x,norm(b))) for x in mul(a,co(b)))
  rr=sub(a,mul(b,q))
  assert abs(norm(rr))<abs(norm(b))
  a,b=b,rr;steps+=1
 return a,steps
def receiver(C,D,Beta,A,b,r):
 H=D*D-Beta*C*C
 assert H==A*b*b and r*r%A==5%A and H>0 and gcd(A,10)==1
 w=(1+r)*pow(2,-1,A)%A
 assert (w*w-w-1)%A==0
 p,step=euclid((A,0),(-w,1))
 assert abs(norm(p))==A
 if norm(p)<0:p=mul(p,(0,1))
 z=tuple(F(b*x,D) for x in p)
 assert norm(z)==1-Beta*F(C,D)**2
 return dict(A=A,b=b,sqrt5=r,gcd_generator=p,steps=step,norm=[str(x) for x in z])

# Independent non-Ready synthetic control with a real repeated split factor.
# Beta=5, c=1/3 gives H=4 and was not chosen: H must be prime to 10.
# Same beta=65 toy as the relative descent, with an exact odd square factor.
be=65;r=F(6,2875);c=4*r/(1-be*r*r);C,D=c.numerator,c.denominator
H=D*D-be*C*C
A=3232932889;b=isqrt(H//A)
assert H==A*b*b and b>1 and gcd(C,D)==1
root=(-2*50986-21427)*pow(21427,-1,A)%A
q=receiver(C,D,be,A,b,root)
# The same fixture can retain the split square factor 29^2 in A.
p0=29;rr=next(i for i in range(p0) if i*i%p0==5);j=p0*p0
rr=(rr+p0*((((5-rr*rr)//p0)*pow(2*rr,-1,p0))%p0))%j
crt2=(root*j*pow(j,-1,A)+rr*A*pow(A,-1,j))%(A*j)
q2=receiver(C,D,be,A*j,1,crt2)

# The four known true odd-depth support factors are not the full modulus.
ps=(131,6551,2470991,16782959)
roots=[pow(5,(p+1)//4,p) for p in ps]
A=reduce(lambda x,y:x*y,ps,1)
crt=sum(r*(A//p)*pow(A//p,-1,p) for p,r in zip(ps,roots))%A
assert crt*crt%A==5
pi,step=euclid((A,0),(-(1+crt)*pow(2,-1,A)%A,1))
if norm(pi)<0:pi=mul(pi,(0,1))
assert norm(pi)==A
print(json.dumps(dict(scope='explicit Euclidean norm construction; true visible product alone not original delta',
 nonready_completed_fixture=q,nonready_retaining_split_square=q2,actual_visible_partial=dict(A=A,sqrt5=crt,pi=pi,steps=step)),indent=2,sort_keys=True))
