#!/usr/bin/env python3
"""Exact complete SS coarse flags and helper residue weights at 673."""
import json,sys,time
from pathlib import Path
from hashlib import sha256
P=Path(__file__).resolve().parent
d=P.parent/'ct-level48-cm192-helper673-framed-t17-r1'
# Only common arithmetic routines, not its 45s T17 execution, are loaded.
raw=(d/'replay_helper673_framed_t17.py').read_text()
assert sha256(raw.encode()).hexdigest()=='2fd85fd268649770688a677451c18769ae3478915e0c879732f46154bf97ffe0'
exec(raw[:raw.index('# Supersingular j via')])
braw=(d/'EXACT-HELPER673-FRAMED-T17.json').read_bytes()
assert sha256(braw).hexdigest()=='2745f5eceb36ad4d40b40e113433cf4da673893f107c538260f616c7d03fa4b1'
base=json.loads(braw)
assert base['field_relation_c']==c
def decode(a):return sum(b<<(w*i) for i,b in a)
def pck(a):
 assert small(a,2)
 return a% (1<<w) + p*((a>>(16*w))&mask)
def up(a):return a%p + ((a//p)<<(16*w))
def mk(r,s):return r%p+p*(s%p)
def plus(a,b):return mk(a%p+b%p,a//p+b//p)
def dif(a,b):return mk(a%p-b%p,a//p-b//p)
def prod(a,b):
 u,v=divmod(a,p);x,y=divmod(b,p)
 return mk(v*y+c*u*x,u*y+v*x)
def conjugate(a):return mk(a%p,-(a//p))
def fvnorm(a):return ((a%p)**2-c*(a//p)**2)%p
def qinv(a):
 x=pow(fvnorm(a),-1,p)
 return prod(x,conjugate(a))
def quo(a,b):return prod(a,qinv(b))
def qsq(a):return prod(a,a)
def qpow(a,e):
 v=1
 while e:
  if e&1:v=prod(v,a)
  a=qsq(a);e>>=1
 return v
root={}
for y in range(p*p):root.setdefault(qsq(y),[]).append(y)
assert len(root)==(p*p+1)//2
js={pck(decode(a)) for a in base['j']}
chart={}; st=time.time()
for X in range(1,p*p):
 X2=qsq(X);X4=qsq(X2)
 for Y in root.get(plus(plus(qsq(X4),prod(14,X4)),1),()):
  y48=prod((p+1)//2,plus(plus(Y,X4),1))
  assert y48
  u=plus(dif(X,2),quo(prod(3,X),y48))
  z=u
  for b in (2,4,16):
   den=plus(z,b)
   if not den:break
   z=quo(qsq(z),den)
  else:
   if not z:continue
   jj=quo(qpow(plus(z,256),3),qsq(z))
   if jj not in js:continue
   f=quo(dif(dif(y48,prod(2,X)),1),X)
   assert (jj,u,f) not in chart
   chart[jj,u,f]=(X,Y)
assert len(chart)==56*96
if '--progress' in sys.argv:print('chart',time.time()-st,file=sys.stderr)

def velu(A,B,K,Ps):
 acc=bb=0
 for x,y in K:
  x2=sq(x);acc=add(acc,add(scl(3,x2),A))
  bb=add(bb,add(add(scl(5,fmul(x,x2)),scl(3,fmul(A,x))),scl(2,B)))
 ta=sub(A,scl(5,acc));tb=sub(B,scl(7,bb))
 assert small(ta,2) and small(tb,2)
 den=iter(batch_inv([sub(x,z) for x,y in Ps for z,v in K],4))
 out=[]
 for x,y in Ps:
  x0,y0=x,y
  for z,v in K:
   sm=fmul(sub(y,v),next(den))
   x1=sub(sub(sq(sm),x),z);y1=sub(fmul(sm,sub(x,x1)),y)
   x0=add(x0,sub(x1,z));y0=add(y0,sub(y1,v))
  assert curve((x0,y0),ta,tb)
  out.append((x0,y0))
 return ta,tb,out

def t8(P8,A):
 p2,p4=toA([JP(2,fromA(P8),A),JP(4,fromA(P8),A)],4)
 u0=p4[0];bb=add(scl(3,sq(u0)),A)
 u=sub(p2[0],u0);v=sub(P8[0],u0)
 assert sq(u)==bb
 k=div(add(v,div(bb,v,4)),u,4)
 z=div(32,sub(k,6),4)
 return pck(z)
def t16(P16,A,B):
 P8,P2=toA([JP(2,fromA(P16),A),JP(8,fromA(P16),A)],4)
 h0=t8(P8,A)
 ta,tb,[P8prime]=velu(A,B,[P2],[P16])
 h1=t8(P8prime,ta)
 sol=[dif(u,2) for u in root.get(plus(4,h1),())]
 sol=[u for u in sol if plus(u,2) and quo(qsq(u),plus(u,2))==h0 and prod(u,plus(u,4))==h1]
 assert len(sol)==1
 return sol[0]

labels={}
C16=[(1,b) for b in range(16)]+[(a,1) for a in range(0,16,2)]
C3=[(1,b) for b in range(3)]+[(0,1)]
for ji,(jj,pts) in enumerate(zip(base['j'],base['order32_and_3_bases'])):
 j=decode(jj); A,B=ab(j)
 U,V,Z,W=[fromA(tuple(decode(x) for x in point)) for point in pts]
 c32=Jgrid(32,U,V,A,4); c3=Jgrid(3,Z,W,A,4)
 P16s=[c32[(2*a)*32+2*b] for a,b in C16]
 first=[t16(P16,A,B) for P16 in P16s]
 for u,v in C3:
  Z3=c3[3*u+v]
  A1,B1,Ps=velu(A,B,[Z3,(Z3[0],neg(Z3[1]))],P16s)
  for i,PP in enumerate(Ps):
   z1=t16(PP,A1,B1)
   q=chart[pck(j),first[i],z1]
   assert q not in labels
   a,b=C16[i];va,vb=((0,1) if a%2 else (1,0))
   labels[q]=[ji,[a,b],[va,vb],[u,v]]
 if '--progress' in sys.argv and (ji+1)%8==0:print('label',ji+1,time.time()-st,file=sys.stderr)
assert len(labels)==len(chart)

sqrt3=next(x for x in range(p) if x*x%p==3)
mm=2+sqrt3
def w48(q):
 X,Y=q
 den=dif(X,1)
 return quo(plus(X,1),den),quo(prod(4,Y),qsq(qsq(den)))
def Frob(q):return tuple(conjugate(a) for a in q)
def hh(q):
 X,Y=q
 t=dif(X,qinv(X))
 y48=prod((p+1)//2,plus(plus(Y,qsq(qsq(X))),1))
 x=quo(y48,qsq(X))
 h=dif(quo(prod(x,t),dif(x,3)),mm)
 assert h
 return h
orbits=[];seen=set();bins={}
for q in sorted(labels):
 if q in seen:continue
 r=w48(q);s=Frob(q)
 assert r!=q and w48(r)==q and w48(s)==Frob(r)
 pool={q,r,s,w48(s)}
 assert all(t in labels for t in pool)
 seen.update(pool)
 h=hh(q);assert hh(r)==h and hh(s)==conjugate(h)
 if s==q:
  kind='fixed'; e=0
 elif s==r:
  kind='frobenius-is-fricke';assert h<p
  e=int(pow(h,(p-1)//2,p)==p-1)
 else:
  kind='four';assert len(pool)==4
  e=int(pow(fvnorm(h),(p-1)//2,p)==p-1)
 bins[(kind,e)]=bins.get((kind,e),0)+1
 orbits.append([q,kind,e,labels[q]])
assert len(seen)==len(labels)
out=dict(p=p,sqrt3=sqrt3,full_marked_labels=len(labels),
          orbits=len(orbits),bins=sorted([kind,weight,cnt] for (kind,weight),cnt in bins.items()),
          records=orbits,scope="complete fixed weights and framed basepoint choices; no selected coefficient")
print(json.dumps(out,sort_keys=True,separators=(',',':')))
