"""Exact 2-descent verification. Self-contained signed-pair local and global tests, descended from the earlier verified checker. Integral equation roots 0,A,D; no CAS required."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod,gcd,isqrt
import json
def sqrt(x):
 x=F(x);q=F(isqrt(x.numerator),isqrt(x.denominator));assert q*q==x;return q
@lru_cache(maxsize=None)
def square(x,p):
 x=F(x);assert x
 if p==0:return (int(x<0),)
 a,b=x.numerator,x.denominator;v=0
 while a%p==0:v+=1;a//=p
 while b%p==0:v-=1;b//=p
 Q=p if p>2 else 8;u=a*pow(b,-1,Q)%Q
 return (v%2,u if p==2 else (0 if pow(u,(p-1)//2,p)==1 else 1))
def slots(x,es):
 return [x-e if x!=e else prod(x-r for r in es if r!=e) for e in es]
def local(es,p):
 size=2 if p==0 else 8 if p==2 else 4
 I={(square(1,p),square(1,p)):'inf'}
 def add(v,x):I.setdefault((square(v[0],p),square(v[1],p)),str(x))
 for e in es:add(slots(e,es),e)
 for i in range(1,80):
  if len(I)==size:break
  for j,t,sgn in product([0,1,-1,2,-2,3,4,5,6,7,8,9,10,11,12,13],es,[-1,1]):
   x=t+sgn*i*F(p or 1)**j
   if x not in es and square(prod(x-e for e in es),p)==square(1,p):add(slots(x,es),x)
 assert len(I)==size,(p,I)
 return I
def sel(es,ps):
 S=(-1,)+ps;D=[prod(q for b,q in zip(bits,S) if b) for bits in product(range(2),repeat=len(S))]
 I={p:local(es,p) for p in (0,)+ps}
 return {(a,b) for a,b in product(D,repeat=2) if all((square(a,p),square(b,p)) in U for p,U in I.items())},I
def sf(x,ps):
 x=F(x);d=prod(p for p in ps if square(x,p)[0])*(-1 if x<0 else 1)
 sqrt(x/d);return d
def run(n,D,e,ps,points,target):
 b=17;theta=409;den=b*D;k=F(n,den);m=b*k*k;C=theta*(1-m); sfC=sqrt(C/b)
 assert n*n+theta*e*e==b*D*D
 A=25*b*n*n-9*den**2;B=16*b*n*n;es=(0,A,B)
 bad=abs(2*A*B*(A-B))
 for p in ps:
  assert all(p%i for i in range(2,isqrt(p)+1))
  while bad%p==0:bad//=p
 assert bad==1
 I,imgs=sel(es,ps)
 gen=[slots(0,es)[:2],slots(A,es)[:2]]
 for x,y in points:
  assert y and y*y==prod(x-ei for ei in es);gen.append(slots(x,es)[:2])
 gen=[(sf(x,ps),sf(y,ps)) for x,y in gen]
 W={(1,1):[]}
 def mul(a,b):return a*b//gcd(a,b)**2
 for i,(s,t) in enumerate(gen):
  W.update({(mul(a,s),mul(b_,t)):c+[i] for (a,b_),c in W.items()})
 assert len(W)==2**len(gen) and set(W)<=I and (1,17) in I and (17,1) in W
 if target=='obstructed':
  assert A==-58225 and B==4352 and len(I)==64 and len(W)==16 and (-1,1) in I and (1,17) not in W
  assert 12**2+241**2==-A
  # At p=3 solve both projective conics on nonzero residues and verify
  # the tangent product cannot vanish; cardinality is immaterial.
  pts=[(a,bb,c,t) for a,bb,c,t in product(range(3),repeat=4) if (a or bb or c or t) and (a*a+bb*bb+A*t*t)%3==0 and (c*c-a*a-B*t*t)%3==0]
  assert pts and all((c-a)*(12*a+241*bb+A*t)%3 for a,bb,c,t in pts)
  local_signs={}
  for p,g in [(5,2),(17,4)]:
   assert (g*g+1)%p==0 and 2*g%p
   val=(-2)*(12+241*g)%p;assert val
   local_signs[p]=1 if p==5 else (1 if pow(val,(p-1)//2,p)==1 else -1)
  assert local_signs=={5:1,17:-1}
  assert all(pow(b,(p-1)//2,p)==1 for p in [137,409])
  extra=dict(nontrivial_pair=[[-1,1],[1,17]],signs={3:1,5:1,17:-1},three_reductions=len(pts),primary_Sha='C2 x C2')
 else:
  assert len(W)==len(I) and (1,17) in W
  extra=dict(marked_subset=W[(1,17)],primary_Sha='0')
  if target=='literal':
   t=F(-1,11);v=(t+k)/(1+b*k*t);Z=sqrt(C*(1-9*b*t*t)*((1+b*k*t)**2-9*b*(t+k)**2))
   r=F(12,1073);pole=17*b*r*r;B0=17*pole;V=B0*B0*(1-pole/17)
   def ac(s):return 4*s/(1+3*b*s*s),2*(1-3*b*s*s)/(1+3*b*s*s)
   aa,cc=ac(t);aa2,cc2=ac(v);et=1-b*aa*aa;et2=1-b*aa2*aa2
   E=B0*et;S=sqrt(V*et/et2);u=17*r;Y1=b*b*u**3*aa*cc;Y2=b*b*(u*S)**3*aa2*cc2
   assert E*S*Y1*Y2 and Y1**2==B0*(B0-E)*(B0+3*E) and Y2**2==B0*S*S*(B0*S*S-E*V)*(B0*S*S+3*E*V)
   extra.update(t=str(t),v=str(v),Z=str(Z),pair={n:str(q) for n,q in zip(['E','S','Y1','Y2'],[E,S,Y1,Y2])})
 la=F(A,B);j=256*(1-la+la*la)**3/(la*la*(1-la)**2)
 return dict(k=str(k),j=str(j),equal_rank_diagnostic=target,integral_roots=es,selmer_size=len(I),rational_span_size=len(W),rank=len(gen)-2,global_points=[[str(x),str(y)] for x,y in points],generators_mod_two=gen,local_image_witnesses={p:list(Dd.values()) for p,Dd in imgs.items()},**extra)
def original(n,ps,pts):
 es=(0,n,-3*n);I,imgs=sel(es,ps);W={(1,1)}
 z=abs(2*n*3*n*4*n)
 for p in ps:
  assert all(p%k for k in range(2,isqrt(p)+1))
  while z%p==0:z//=p
 assert z==1
 for x,y in pts:assert y and y*y==prod(x-a for a in es)
 for x in [0,n]+[x for x,y in pts]:
  a,b=[sf(q,ps) for q in slots(x,es)[:2]]
  W|={(u*a//gcd(u,a)**2,v*b//gcd(v,b)**2) for u,v in W}
 assert len(W)==len(I)==32 and W==I and (17,1) in W
 return dict(n=n,rank=3,primary_Sha='0',selmer_size=len(I),rational_points=[[str(x),str(y)] for x,y in pts],ordered_marking=[17,1],local_image_witnesses={p:list(V.values()) for p,V in imgs.items()})
if __name__=='__main__':
 outputs=[run(4,5,1,(2,3,5,17,137,409),[(-37264,5701392),(13600,3005600)],'obstructed'),
 run(256,89,13,(2,3,13,17,409,426487),[(27852800,75854315520),(F(78687799251200,1042441),F(580011360697999376640,1064332261))],'literal'),
 run(569,209,32,(2,3,17,409,569,88177),[(8748944,102819847680),(F(14020897424,625),F(746590892179968,15625)),(F(1497070864,81),F(61320022589440,729)),(F(56818064,25),F(8132917542912,125)),(F(595945744,25),F(1870851312128,125))],'rank-five')]
 assert len(set(o['j'] for o in outputs))==3 and [o['rank'] for o in outputs]==[2,2,5]
 b0=F(204,1073)**2; VV=(17*b0)**2*(1-b0/17);E=F(outputs[1]['pair']['E']);sqrt(E/(-221));sqrt(E*VV/(-90389))
 base=[original(-221,(2,3,13,17),[(-204,1734),(-169,2704),(4131,249696)]),
       original(-90389,(2,3,13,17,409),[(-31212,23632686),(302379,60884208),(F(-252841801,2809),F(521673011560,148877))])]
 print(json.dumps(dict(matching=outputs,original=base),indent=2))
