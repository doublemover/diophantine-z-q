"""Exact 2-descent verification. Integral equation roots 0,A,D; no CAS required."""
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
def run(n,dh,ps,points,rank):
 be=17;th=577;r=F(12,55);pole=17*be*r*r;B=17*pole;V=B*B*(1-pole/17)
 den=17*dh;k=F(n,den);m=be*k*k;C=th*(1-m)
 assert sqrt(C/be) and pole==(F(204,55))**2 and (1-pole/17)==F(th,55**2)
 A=25*be*n*n-9*den**2;D=16*be*n*n;es=(0,A,D)
 sf(2*A*D*(A-D),ps); assert all(all(p%d for d in range(2,isqrt(p)+1)) for p in ps)
 # Verify listed support exhausts bad primes, including those of even valuation.
 z=abs(2*A*D*(A-D))
 for p in ps:
  while z%p==0:z//=p
 assert z==1
 I,imgs=sel(es,ps)
 gens = [slots(es[0],es)[:2],slots(es[1],es)[:2]]
 for x,y in points:
  assert y!=0 and y*y==prod(x-e for e in es)
  gens.append(slots(x,es)[:2])
 gen=[(sf(a,ps),sf(b,ps)) for a,b in gens]
 def mul(x,y):return x*y//gcd(x,y)**2
 W={(1,1)}
 for a,b in gen:W|={(mul(x,a),mul(y,b)) for x,y in W}
 assert W==I and len(I)==2**(rank+2) and all(g in I for g in [(1,be),(be,1)])
 t=F(-1,3);v=(t+k)/(1+be*t*k)
 y=sqrt(C*(1-9*be*t*t)*((1+be*k*t)**2-9*be*(t+k)**2))
 def ac(t):return 4*t/(1+3*be*t*t),2*(1-3*be*t*t)/(1+3*be*t*t)
 a,c=ac(t);h,d=ac(v);e=1-be*a*a;e2=1-be*h*h
 u=17*r;E=B*e;S=sqrt(V*e/e2);y1=be**2*u**3*a*c;y2=be**2*(u*S)**3*h*d
 f=lambda x,w:x*(x-w)*(x+3*w)
 assert E*S*y1*y2 and y1*y1==f(B,E) and y2*y2==f(B*S*S,E*V)
 la=F(A,D);j=256*(1-la+la*la)**3/(la*la*(1-la)**2)
 return dict(slope=str(k),j=str(j),theta=th,t=str(t),actual_H_y=str(y),roots=es,selmer_size=len(I),rank=rank,primary_Sha='0',rational_generators_mod_two=gen,points=[[str(x),str(y)] for x,y in points],local_image_witness_x={p:list(D.values()) for p,D in imgs.items()},pointpair={u:str(q) for u,q in zip(['E','S','y1','y2'],[E,S,y1,y2])})
if __name__=='__main__':
 print(json.dumps([run(16,7,(2,3,17,577,1097),[(-18496,499392),(108800,23304960),(147968,43946496),(-2312,1648456)],4),run(149,43,(2,3,17,149,577,1063),[(9435425,12415132215),(F(272136017,4),F(4137175447353,8))],2)],indent=2))
