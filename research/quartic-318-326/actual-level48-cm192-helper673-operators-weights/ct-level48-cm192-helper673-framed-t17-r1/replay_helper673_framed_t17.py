#!/usr/bin/env python3
"""Compressed p=673 exact supersingular framed T17 and relative Frob."""
from fractions import Fraction
from functools import lru_cache
from math import comb
import json, random, sys, time
from pathlib import Path
p=673
w=24
mask=(1<<w)-1
n=32
Q=p**n
step_t=1<<w
M17=p**16-1
M96=p*p-1
T=sum(1<<(w*i) for i in range(n))
ALLp=T*p
c=pow(next(i for i in range(2,p) if pow(i,(p-1)//2,p)!=1),21,p)
assert pow(c,16,p)==p-1 and pow(p,32,1024)==1 and pow(p,16,1024)!=1
def norm(a):
 return sum(((a>>(w*i))&mask)%p<<(w*i) for i in range(n))
def add(a,b):return norm(a+b)
def sub(a,b):return norm(a+ALLp-b)
def neg(a):return sub(0,a)
def fmul(a,b):
 r=a*b
 return sum(((((r>>(w*i))&mask)+c*((r>>(w*(i+n)))&mask))%p)<<(w*i) for i in range(n))
def scl(a,b):return norm((a%p)*b)
def ex(a,k):
 z=1
 while k:
  if k&1:z=fmul(z,a)
  k>>=1
  if k:a=fmul(a,a)
 return z
def inv(a,deg=32):
 assert a
 if a<p:return pow(a,-1,p)
 return ex(a,p**deg-2)
def div(a,b,deg=32):return fmul(a,inv(b,deg))
def sq(a):return fmul(a,a)
def enc(a):return [(i,(a>>(w*i))&mask) for i in range(n) if (a>>(w*i))&mask]
def fr(a):return ex(a,p)
def small(a,deg):
 return all(i%(n//deg)==0 for i,_ in enc(a))
assert ex(step_t,32)==c
def sqroot(a,deg):
 if not a:return 0
 ff=p**deg
 if ex(a,(ff-1)//2)!=1:return None
 o=ff-1;e=0
 while o%2==0:o//=2;e+=1
 z=1<<(w*(n//deg)) if deg>1 else c
 R=ex(a,(o+1)//2);t=ex(a,o);g=ex(z,o)
 while t!=1:
  v=t;i=0
  while v!=1:v=sq(v);i+=1
  assert i<e,(deg,i,e,enc(a))
  g1=ex(g,1<<(e-i-1));g=sq(g1)
  R=fmul(R,g1);t=fmul(t,g);e=i
 assert sq(R)==a
 return R
def batch_inv(xs,deg=32):
 prefixes=[]; x=1
 for z in xs:
  assert z;prefixes.append(x);x=fmul(x,z)
 y=inv(x,deg);v=[]
 for x,z in zip(reversed(prefixes),reversed(xs)):
  v.append(fmul(x,y));y=fmul(z,y)
 assert y==1
 return v[::-1]

def JD(P,A):
 if P is None:return None
 x,y,z=P
 if not y:return None
 xx=sq(x);yy=sq(y);yyyy=sq(yy);zz=sq(z)
 s=scl(2,sub(sub(sq(add(x,yy)),xx),yyyy))
 m=add(scl(3,xx),fmul(A,sq(zz)))
 h=sub(sq(m),scl(2,s))
 return h,sub(fmul(m,sub(s,h)),scl(8,yyyy)),scl(2,fmul(y,z))
def JA(P,R,A):
 if P is None:return R
 if R is None:return P
 x,y,z=P;X,Y,Z=R
 a=sq(z);b=sq(Z)
 U=fmul(x,b);V=fmul(X,a)
 J=fmul(y,fmul(Z,b));K=fmul(Y,fmul(z,a))
 H=sub(V,U);r=sub(K,J)
 if not H:return JD(P,A) if not r else None
 hh=sq(H);hhh=fmul(H,hh);u=fmul(U,hh)
 h=sub(sub(sq(r),hhh),scl(2,u))
 return h,sub(fmul(r,sub(u,h)),fmul(J,hhh)),fmul(H,fmul(z,Z))
def JP(k,P,A):
 out=None
 while k:
  if k&1:out=JA(out,P,A)
  k>>=1
  if k:P=JD(P,A)
 return out
def toA(L,deg):
 iz=iter(batch_inv([P[2] for P in L if P is not None],deg))
 ret=[]
 for P in L:
  if P is None:ret.append(None);continue
  x,y,z=P;i=next(iz);ii=sq(i)
  ret.append((fmul(x,ii),fmul(y,fmul(ii,i))))
 return ret
def fromA(P):return None if P is None else (P[0],P[1],1)
def curve(P,A,B):
 if P is None:return True
 x,y=P;return sq(y)==add(fmul(x,add(sq(x),A)),B)
def Jgrid(n,P,R,A,deg):
 U=[None];V=[None]
 for _ in range(1,n):
  U.append(JA(U[-1],P,A));V.append(JA(V[-1],R,A))
 assert JA(U[-1],P,A) is None and JA(V[-1],R,A) is None
 C=toA([JA(i,j,A) for i in U for j in V],deg)
 assert len(set(C))==n*n
 return C
def cal_j(A,B):
 v=scl(4,fmul(sq(A),A))
 return div(scl(1728,v),add(v,scl(27,sq(B))),2)
def ab(j):
 c0=div(j,sub(1728%p,j),2)
 return scl(3,c0),scl(2,c0)
# Supersingular j via exact factorization of Deuring's Legendre Hasse polynomial.
m=(p-1)//2
coeff=[comb(m,k)**2%p for k in range(m+1)]
fac=json.loads(Path(__file__).with_name("EXACT-LEGENDRE-HASSE-FACTORS.json").read_text())
assert len({tuple(c) for c in fac})==len(fac)
P=[1]
for co in fac:
 assert co[0]==1 and len(co) in (2,3)
 if len(co)==3:assert pow((co[1]**2-4*co[2])%p,(p-1)//2,p)==p-1
 R=[0]*(len(P)+len(co)-1)
 for i,a in enumerate(P):
  for j,b in enumerate(reversed(co)):R[i+j]=(R[i+j]+a*b)%p
 P=R
assert P==coeff
js=set()
for co in fac:
 if len(co)==2:la=[(-co[1])%p]
 else:
  d=sqroot((co[1]*co[1]-4*co[2])%p,2)
  assert d is not None
  la=[scl(pow(2,-1,p),add((-co[1])%p,d)),scl(pow(2,-1,p),sub((-co[1])%p,d))]
 for l in la:
  assert l not in (0,1)
  u=add(sub(1,l),sq(l))
  j=div(scl(256,fmul(sq(u),u)),fmul(sq(l),sq(sub(1,l))),2)
  assert j not in (0,1728%p)
  js.add(j)
js=sorted(js); assert len(js)==56
models=[]
RNG=random.Random(673)
start=time.time()
def random_pt(A,B,deg):
 while True:
  x=sum(RNG.randrange(p)<<(w*i) for i in range(0,n,n//deg))
  y=sqroot(add(fmul(x,add(sq(x),A)),B),deg)
  if y is not None:return x,y,1
def basis17(A,B):
 acc=[]
 for k in range(120):
  R=random_pt(A,B,32);P=JP(M17//17,R,A)
  if P is None:continue
  assert JP(17,P,A) is None
  if not acc:
   acc.append(P)
   C=toA([JP(t,P,A) for t in range(17)],32)
   continue
  if toA([P],32)[0] not in C:
   return acc[0],P
 raise Exception("small entropy")
def basis96(A,B):
 b=[]
 for k in range(120):
  R=random_pt(A,B,4);u=JP(M96//96,R,A)
  a,z=toA([JP(48,u,A),JP(32,u,A)],4)
  if a is None or z is None:continue
  assert JP(96,u,A) is None
  if b and a!=b[1] and z not in (b[2],(b[2][0],neg(b[2][1]))):return b[0],u
  if not b:b=[u,a,z]
 raise Exception("small entropy")
for j in js:
 A,B=ab(j); assert cal_j(A,B)==j
 P,Q0=basis96(A,B)
 P32,Q32,P3,Q3=[JP(k,R,A) for k,R in ((3,P),(3,Q0),(32,P),(32,Q0))]
 d32={v:i for i,v in enumerate(Jgrid(32,P32,Q32,A,4))}
 d3={v:i for i,v in enumerate(Jgrid(3,P3,Q3,A,4))}
 qdata=toA([P32,Q32,P3,Q3],4)
 R,S0=basis17(A,B)
 U=Jgrid(17,R,S0,A,32)
 models.append(dict(j=j,A=A,B=B,q=qdata,d32=d32,d3=d3,points17=U))
 if "--progress" in sys.argv and len(models)%8==0:print('models',len(models),round(time.time()-start,2),file=sys.stderr)
idx={m['j']:i for i,m in enumerate(models)}
def VELU(x,A,B,K):
 AP=BP=0
 for z,w0 in K:
  z2=sq(z);AP=add(AP,add(scl(3,z2),A))
  BP=add(BP,add(add(scl(5,fmul(z2,z)),scl(3,fmul(A,z))),scl(2,B)))
 ta=sub(A,scl(5,AP));tb=sub(B,scl(7,BP))
 assert small(ta,2) and small(tb,2)
 r=[]
 iv=iter(batch_inv([sub(t,z) for t,_ in x for z,_ in K],32))
 for t,u in x:
  tx,ty=t,u
  for z,w0 in K:
   sl=fmul(sub(u,w0),next(iv))
   sx=sub(sub(sq(sl),t),z)
   sy=sub(fmul(sl,sub(t,sx)),u)
   tx=add(tx,sub(sx,z));ty=add(ty,sub(sy,w0))
  r.append((tx,ty));assert curve((tx,ty),ta,tb)
  assert small(tx,4) and small(ty,4)
 return ta,tb,r
def mat(pts,q):
 m=[]
 for t,y in enumerate(pts):
  ell=32 if t<2 else 3
  k=q['d32' if ell==32 else 'd3'][y]
  m.append(list(divmod(k,ell)))
 return m
edges=[]; FROB=[]
for j,m in enumerate(models):
 rows=[]
 for ell in range(18):
  pc=[m['points17'][(z*17+(z*ell)%17) if ell<17 else z] for z in range(1,17)]
  assert len(set(pc))==16 and all(pc)
  ta,tb,rr=VELU(m['q'],m['A'],m['B'],pc)
  q=cal_j(ta,tb);d=idx[q]; dd=models[d]
  a,b=div(ta,dd['A'],2),div(tb,dd['B'],2)
  u2=div(b,a,2);u=sqroot(u2,4)
  assert u and sq(u2)==a and fmul(sq(u2),u2)==b
  rr=[(div(x,u2,4),div(y,fmul(u,u2),4)) for x,y in rr]
  assert all(curve(P,dd['A'],dd['B']) for P in rr)
  mm=mat(rr,dd)
  dt=lambda a,b:(a[0]*b[1]-a[1]*b[0])
  assert dt(*mm[:2])%2==1 and dt(*mm[2:])%3!=0
  rows.append([d,mm])
 edges.append(rows)
 nxt=idx[fr(m['j'])];re=[(fr(x),fr(y)) for x,y in m['q']]
 mm=mat(re,models[nxt]);FROB.append([nxt,mm])
 if "--progress" in sys.argv and (j+1)%8==0:print('edges',j+1,round(time.time()-start,2),file=sys.stderr)
# Check A→A relative I² Frobenius acts by a common sign on the transported degree96 basis.
def pmul(A,B,l):
 return [[sum(a*b for a,b in zip(x,y))%l for y in zip(*B)] for x in A]
for j,(a,mat0) in enumerate(FROB):
 b,mat1=FROB[a];assert b==j
 L=[pmul(mat0[:2],mat1[:2],32),pmul(mat0[2:],mat1[2:],3)]
 assert L in [[[[s,0],[0,s]],[[t,0],[0,t]]] for s,t in ((1,1),(31,2))]
def mprod(A,B):
 return pmul(A[:2],B[:2],32)+pmul(A[2:],B[2:],3)
def sign_both(A):
 r=[[(-a)%32 for a in row] for row in A[:2]]+[ [(-a)%3 for a in row] for row in A[2:]]
 return min(A,r)
diag17=[[17,0],[0,17],[2,0],[0,2]]
for x,rows in enumerate(edges):
 for y,mm in rows:
  assert any(z==x and sign_both(mprod(mm,mm1))==sign_both(diag17)
             for z,mm1 in edges[y])
 y,A=FROB[x]
 lhs=sorted((FROB[z][0],sign_both(mprod(C,FROB[z][1]))) for z,C in rows)
 rhs=sorted((z,sign_both(mprod(A,C))) for z,C in edges[y])
 assert lhs==rhs
out=dict(p=p,field_relation_c=c,legendre_hasse_factors=sorted(fac),
         j=[enc(j) for j in js],
         order32_and_3_bases=[[ [enc(x),enc(y)] for x,y in m['q']] for m in models],
         T17=edges,FrobI=FROB,full_frame_states=len(js)*6144,checked_dual_edges=len(js)*18,checked_frobenius_commutation_rows=len(js),scope="exact p673 fixed framed Hecke donor, no moving n or mark")
print(json.dumps(out,sort_keys=True,separators=(',',':')))
