"""Exact unrestricted trace on a known UNEQUAL full-mark rational pair; stdlib only."""
from fractions import Fraction as Q
from math import isqrt
import json
k,theta,m=17,409,3026
def sqrt(x):
 x=Q(x);a,b=isqrt(x.numerator),isqrt(x.denominator)
 assert a*a==x.numerator and b*b==x.denominator
 return Q(a,b)
def field(a=0,b=0,c=0,d=0): return tuple(map(Q,(a,b,c,d)))
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def neg(x):return tuple(-a for a in x)
def sub(x,y):return add(x,neg(y))
def mul(x,y):
 z=[Q(0)]*4
 for i,a in enumerate(x):
  for j,b in enumerate(y): z[i^j]+=a*b*(k if i&j&1 else 1)*(theta if i&j&2 else 1)
 return tuple(z)
def conj(x,i):return tuple(a*(-1 if i&j else 1) for j,a in enumerate(x))
def div(x,y):
 v=mul(conj(y,1),mul(conj(y,2),conj(conj(y,1),2)));c=mul(y,v)
 assert c[0] and c==field(c[0]);return tuple(a/c[0] for a in mul(x,v))
def sq(x):return mul(x,x)
def on(p,n):
 x,y=p;return sq(y)==mul(x,add(sq(sub(x,field(2*n))),field(12*n*n)))
def dualhalf(n,xq):
 y=sqrt(xq*(xq-n)*(xq+3*n));u=field(0,sqrt(xq/k))
 x=mul(field(2),add(field(n+xq),div(field(y),u)));y=mul(field(2),mul(u,x))
 assert on((x,y),n) and sq(div(y,mul(field(2),x)))==field(xq)
 return x,y
def plus(p,q,n):
 x,y=p;u,v=q;l=div(sub(y,v),sub(x,u));w=sub(add(sq(l),field(4*n)),add(x,u));out=(w,sub(mul(l,sub(x,w)),y))
 assert on(out,n);return out
def sf(x):
 n=Q(x).numerator*Q(x).denominator;i=2
 while i*i<=n:
  while n%(i*i)==0:n//=i*i
  i+=1
 return n
def control(x1,x2):
 c1,c2=sf(x1-m),sf(x2-m*theta)
 p=dualhalf(m,x1);q=dualhalf(m*theta,x2);q=(div(q[0],field(theta)),div(q[1],field(0,0,theta)))
 assert on(q,m)
 R=plus(p,q,m);Z=sub(div(R[0],field(m)),field(2));a,aa,b,bb=Z;assert aa==bb==0 and b
 N=a*a-theta*b*b;s=sqrt(N+4*a+4);w=sqrt((N-12)**2+48*a*a);h=sqrt(6*(w+12-N)/k)
 r=k*(h/12)**2
 assert theta*b*b==(r-1)*(12+a*a/r) and s*s==(a+2*r)**2/r+16*(1-r)
 d=2*(a*a+theta*b*b+12+w);J=(w-N-12)/6
 assert theta*d*J==(theta*b/3)**2*(6*(w+12-N))
 return dict(beta=k,theta=theta,source_twists=[str(m),str(m*theta)],secondary_classes=[c1,c2],Z_rational=str(a),Z_irrational_coefficient=str(b),s=str(s),w=str(w),h=str(h),r=str(r),criterion="all exact, both original abscissa classes 17")
if __name__=='__main__':
 prepared=control(Q(71825,16),Q(5161217,4))
 m=Q(34,19);theta=174
 unequal=control(Q(17),17*Q(174,19)**2)
 assert unequal['secondary_classes']==[19,87]
 print(json.dumps(dict(prepared_unindexed=prepared,independent_unequal_control=unequal),indent=2))
