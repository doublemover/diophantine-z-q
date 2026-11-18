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

N=6953;roots=[0,9*N,-3*N];ans,imgs=screen(roots,[2,3,17,409],17)
assert ans==[3,1227];assert all((sqcl(1,p),sqcl(409,p)) in J for p,J in imgs.items())
assert 17*409==N and 35**2-409==51*4**2 and 16**2-409==-153
tab={}
for p,K,w in [(2,18,20027),(3,9,1537),(17,5,536468)]:
 M=p**K;assert (w*w-409)%M==0
 a,b,c,t=1,w,-w,0
 l=triple(a,b,c,t);hh=[hl(x,g,p) for x,g in zip(l,(17,3,51))]
 assert all(v(x,p)[0]+(4 if p==2 else 1)<K for x in l)
 tab[str(p)]={'sqrt409_mod':w,'modulus':M,'hilbert':hh}
assert [prod(x['hilbert']) for x in tab.values()]==[-1,1,1]
for a in [17,3,51,-153]:assert pow(a%409,204,409)==1
assert sum(pow(17,d,409)==1 for d in [204])==1
for p in [17,409]:assert all(p%q for q in range(2,1+int(p**.5)))
from json import dumps
print(dumps({'roots':roots,'first17_second_coordinates':ans,'other_selmer_tested':[1,409],'local_image_sizes':{str(p):len(J) for p,J in imgs.items()},'tangent_factor_certificates':tab,'ellrank_used':False},indent=2))
