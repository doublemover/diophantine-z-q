from math import prod
from itertools import product
from fractions import Fraction as F
from functools import cache

from math import gcd
@cache
def sqcl(x,p):
 if p==0:return x<0
 assert x!=0;v=0;a,b=F(x).as_integer_ratio()
 while not a%p:v+=1;a//=p
 while not b%p:v-=1;b//=p
 m=p if p>2 else 8;u=a*pow(b,-1,m)%m
 return (v%2,u if p==2 else pow(u,(p-1)//2,p))
def local(roots,p):
 size=2 if p==0 else 8 if p==2 else 4;D={};rs=roots
 def add(a,b,x):
  D.setdefault((sqcl(a,p),sqcl(b,p)),x)
 add(1,1,'infinity')
 for x in rs:
  v=[x-y if x!=y else prod(x-z for z in rs if z!=x) for y in rs];add(*v[:2],str(x))
 for i in range(1,100):
  if len(D)==size:break
  for k in (0,-1,1,-2,2,3,4):
   for t in roots:
    for sign in (1,-1):
     x=t+sign*i*F(p or 1)**k
     if x not in rs and sqcl(prod(x-r for r in rs),p)==sqcl(1,p):add(x,x-rs[1],str(x))
 assert len(D)==size,(p,size,len(D));return D
def screen(roots,qs,first):
 S=[-1]+qs;ds=[prod(q for q,b in zip(S,bb) if b) for bb in product((0,1),repeat=len(S))];rs={p:local(roots,p) for p in [0]+qs}
 return sorted(d for d in ds if all((sqcl(first,p),sqcl(d,p)) in R for p,R in rs.items())),rs

def v(x,p):
 a=0;assert x
 while not x%p:x//=p;a+=1
 return a,x
def hl(a,b,p):
 if not p:return -1 if max(a,b)<0 else 1
 i,u=v(a,p);j,t=v(b,p)
 if p==2:return (-1)**(((u-1)//2*((t-1)//2)+i*((t*t-1)//8)+j*((u*u-1)//8))%2)
 return (-1)**(((p-1)//2*i*j)%2)*(1 if pow(u%p,(p-1)//2,p)==1 else -1)**(j%2)*(1 if pow(t%p,(p-1)//2,p)==1 else -1)**(i%2)
def triple(A,b,c,t):return [c-b,35*c-409*A-204*t,16*b-409*A+153*t]

def all_sel(roots,qs):
 S=[-1]+qs;D=[prod(q for q,b in zip(S,bb) if b) for bb in product(range(2),repeat=len(S))];images={p:local(roots,p) for p in [0]+qs}
 return [(x,y) for x in D for y in D if all((sqcl(x,p),sqcl(y,p)) in I for p,I in images.items())]
def sf(x):
 d=(abs(x.numerator)*x.denominator if isinstance(x,F) else abs(x));j=2;t=1 if x>0 else -1
 while j*j<=d:
  while d%(j*j)==0:d//=j*j
  j+=1
 return d*t
def square_rep(x,S):
 from math import isqrt
 v=1 if x>0 else -1
 for p in S:
  a,b=F(x).as_integer_ratio();i=0
  while a%p==0:i+=1;a//=p
  while b%p==0:i-=1;b//=p
  if i%2:v*=p
 y=F(x)/v; assert isqrt(y.numerator)**2==y.numerator and isqrt(y.denominator)**2==y.denominator
 return v
def delta(P,n,qs):
 x,y=P;assert y*y==x*(x-n)*(x+3*n)
 return (square_rep(x,qs),square_rep(x-n,qs))
def exprod(a,b):return sf(a*b)
def span(g):
 V={(1,1)}
 for a,b in g:V|={(exprod(x,a),exprod(y,b)) for x,y in V}
 return V
sets={};rational={}
for n,qs,expected in [(6953,[2,3,17,409],32),(-20859,[2,3,17,409],16),(3026,[2,3,17,89],16),(1237634,[2,3,17,89,409],64)]:
 roots=(0,n,-3*n) if n>0 else (0,-3*n,n)
 I=all_sel(roots,qs);assert len(I)==expected;sets[n]=I
 S=[(square_rep(-3*n*n,qs),square_rep(-roots[1],qs)),(square_rep(roots[1],qs),square_rep(roots[1]*(roots[1]-roots[2]),qs))]
 Ps={6953:[(F(1483737111368925361,213060877526025),F(142997095811431209398652784,3109965470200764145125))],-20859:[],3026:[(F(71825,16),F(19104345,64)),(31250,5964000)],1237634:[(F(5161217,4),F(4664906505,8)),(F(33796306,9),F(226864398880,27))]}[n]
 S += [delta(P,n,qs) for P in Ps];V=span(S);assert len(V)==(1<<len(S)) and V<=set(I);rational[n]=S
assert (1,409) in sets[1237634] and (89,1) in sets[1237634]
n=1237634;assert 10225**2-409*383**2==n*6**2 and 6*n//409==18156
loc={}
for p,X0 in [(3,2),(89,26)]:
 assert (X0*X0-409)%p==0 and (2*X0)%p!=0
 a=-2*(25*X0+383);assert a%p;loc[p]=hl(a,89,p)
assert loc=={3:1,89:-1} and 89%8==1 and pow(89,8,17)==pow(89,204,409)==1
from json import dumps
print(dumps({'selmer_sizes':{n:len(I) for n,I in sets.items()},'independent_rational_pairs':rational,'new_pairing_nontrivial_arguments_at_p':loc,'new_free_second_row':[[1,409],[89,1]],'CAS_used_for_verification':False},indent=2))
