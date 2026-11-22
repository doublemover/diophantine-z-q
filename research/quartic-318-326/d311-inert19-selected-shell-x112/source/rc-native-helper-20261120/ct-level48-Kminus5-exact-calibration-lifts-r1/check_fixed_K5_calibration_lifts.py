#!/usr/bin/env python3
"""Exact integer ring class polynomials and named lifts of the actual calibration flags."""
import json,math,sys
from pathlib import Path
from hashlib import sha256
from sympy import Matrix,Poly,Symbol,factor_list,resultant
p=29;L=175
root=Path(__file__).resolve().parents[2]
cal=root/'high-hom-1120/heegner-compressed-trace/original-inert29-CM-real-ideal-r2'
assert sha256((cal/'SHA256SUMS').read_bytes()).hexdigest()=='c763e955648ab6ecc2873fdf2250e69478270cc6cf07a7b63d0c87f5aa528517'
for ln in (cal/'SHA256SUMS').read_text().splitlines():
 h,n=ln.split(); assert sha256((cal/n).read_bytes()).hexdigest()==h
sys.path.insert(0,str(cal)); import calibration_end_rings as C
m=C.m

def mul(a,b):
 r={}
 for i,u in a.items():
  for j,v in b.items():
   if i+j<=L:r[i+j]=r.get(i+j,0)+u*v
 return {i:v for i,v in r.items() if v}
A={0:1}
for n in range(1,L+1): A=mul(A,{n*j:(-1)**j*math.comb(24,j) for j in range(1+min(24,L//n))})
AI={0:1}
for n in range(1,L+1):AI[n]=-sum(A.get(i,0)*AI[n-i] for i in range(1,n+1))
E={0:1,**{k:240*sum(j**3 for j in range(1,k+1) if k%j==0) for k in range(1,L+1)}}
J={i-1:v for i,v in mul(mul(mul(E,E),E),AI).items()}
assert [J[i] for i in range(-1,3)]==[1,744,196884,21493760]
a,b=Symbol('a'),Symbol('b')

def modular_ij(l):
 d=l+1
 D=[{0:1}]
 for i in range(d):D.append(mul(D[-1],J))
 B=[{l*i:v for i,v in u.items()} for u in D]
 ij=[(i,j) for i in range(d+1) for j in range(i,d+1) if j<d or i==0]
 def pq(i,j):
  X=mul(D[i],B[j]);Y=mul(D[j],B[i]) if i!=j else {}
  return {k:X.get(k,0)+Y.get(k,0) for k in X.keys()|Y.keys()}
 V=[pq(i,j) for i,j in ij]
 T=Matrix([[u.get(k,0) for u in V] for k in range(-d*d,2*d*d+1)]).nullspace()
 assert len(T)==1
 u=T[0]/T[0][ij.index((0,d))]; assert all(z.q==1 for z in u)
 return [[i,j,int(z)] for (i,j),z in zip(ij,u) if z]

def phi(terms):
 return sum(c*(a**i*b**j + (a**j*b**i if i!=j else 0)) for i,j,c in terms)
T={l:modular_ij(l) for l in (2,3,5)}; P={l:phi(t) for l,t in T.items()}
F=factor_list(Poly(P[5].subs(b,a),a))[1]
assert sorted(v.degree() for v,k in F).count(2)==1,[(v.as_expr(),k) for v,k in F]
H={1:next(v.monic() for v,k in F if v.degree()==2)}
assert H[1].all_coeffs()==[1,-1264000,-681472000]
def qresult(Hd,l,quot,expected):
 h=Poly(resultant(Hd.as_expr(),P[l],a),b).exquo(Poly(quot.subs(a,b),b))
 h=Poly(h.as_expr().subs(b,a),a)
 assert h.degree()==expected and h.is_monic and h.is_sqf and all(c.q==1 for c in h.all_coeffs())
 return h
H[2]=qresult(H[1],2,H[1].as_expr(),4)
H[3]=qresult(H[1],3,H[1].as_expr()**2,4)
H[4]=qresult(H[2],2,H[1].as_expr()**2,8)
H[6]=qresult(H[2],3,H[2].as_expr()**2,8)
H[12]=qresult(H[4],3,H[4].as_expr()**2,16)
HC={k:[int(c) for c in v.all_coeffs()] for k,v in H.items()}
for j in C.JS:
 if C.trace[j][1]!=-20:continue
 k=C.conductor(j)
 h=0
 for a0 in HC[k]:h=m.add(m.mul(h,j),a0%29)
 assert h==0,(j,k)

def line(q):return [q%29,q//29]
class Ring:
 def __init__(self,n):self.q=n
 def const(self,k):return (k%self.q,0)
 def add(self,a,b):return ((a[0]+b[0])%self.q,(a[1]+b[1])%self.q)
 def neg(self,a):return ((-a[0])%self.q,(-a[1])%self.q)
 def sub(self,a,b):return self.add(a,self.neg(b))
 def mul(self,a,b):
  u,v=a;w,z=b
  return ((u*w+2*v*z)%self.q,(u*z+v*w)%self.q)
 def pw(self,a,k):
  o=(1,0)
  while k:
   if k&1:o=self.mul(o,a)
   a=self.mul(a,a);k//=2
  return o
 def div(self,a,b):
  x,y=b;t=pow((x*x-2*y*y)%self.q,-1,self.q)
  return self.mul(a,(x*t%self.q,-y*t%self.q))
 def fx(self,x,y):return self.sub(self.pw(y,2),self.add(self.add(self.pw(x,8),self.mul((14,0),self.pw(x,4))),(1,0)))
 def j(self,x,y):
  y48=self.div(self.add(self.add(y,self.pw(x,4)),(1,0)),(2,0))
  t=self.add(self.sub(x,(2,0)),self.div(self.mul((3,0),x),y48))
  for c in (2,4,16):t=self.div(self.pw(t,2),self.add(t,(c,0)))
  return self.div(self.pw(self.add(t,(256,0)),3),self.pw(t,2))
 def w48(self,x,y):
  d=self.sub(x,(1,0))
  return self.div(self.add(x,(1,0)),d),self.div(self.mul((4,0),y),self.pw(d,4))
 def h(self,k,x):
  v=(0,0)
  for a0 in HC[k]:v=self.add(self.mul(v,x),self.const(a0))
  return v
 def fun(self,x,y,k):return self.fx(x,y),self.h(k,self.j(x,y))

def lift(q):
 x,y=map(lambda z:tuple(line(z)),q)
 ja,jb=m.j48(*q),m.j48(*m.w48(*q)); c,d=C.conductor(ja),C.conductor(jb)
 assert ja not in (0,17,2,25) and jb not in (0,17,2,25)
 r=Ring(29**2);s=Ring(29)
 base=r.fun(x,y,c)
 cols=[]
 for dx,dy in [(29,0),(0,29)]:
  xx=(x[0]+dx,x[1]);yy=(y[0]+dy,y[1]); ff=r.fun(xx,yy,c)
  vv=[r.sub(u,v) for u,v in zip(ff,base)]; assert all(not z%29 for zz in vv for z in zz)
  cols.append([tuple(z//29 for z in zz) for zz in vv])
 (u,w),(v,z)=cols;det=s.sub(s.mul(u,z),s.mul(v,w));assert det!=(0,0)
 row=[29]
 for k in range(1,6):
  pp=29**k;r=Ring(pp*29);f,g=r.fun(x,y,c)
  assert all(not a0%pp for zz in (f,g) for a0 in zz)
  F,G=tuple((-a0//pp)%29 for a0 in f),tuple((-a0//pp)%29 for a0 in g)
  dx=s.div(s.sub(s.mul(F,z),s.mul(v,G)),det);dy=s.div(s.sub(s.mul(u,G),s.mul(F,w)),det)
  x=tuple(a0+pp*b0 for a0,b0 in zip(x,dx));y=tuple(a0+pp*b0 for a0,b0 in zip(y,dy))
  assert r.fun(x,y,c)==((0,0),(0,0))
  assert r.h(d,r.j(*r.w48(x,y)))==(0,0)
  row.append(pp*29)
 return dict(flag=q,source_j=ja,target_j=jb,source_conductor=c,target_conductor=d,Jacobian_det=det,x=x,y=y)

rows=json.loads((cal/'EXACT-REAL-CM-CUBIC.json').read_text())['signed_whole_packets']
q={tuple(Q) for l,D,QQ,e in rows for Q in QQ}
assert len(q)==32
out=[lift(Q) for Q in sorted(q)]
print(json.dumps(dict(scope='Actual fixed K=-5 calibration char-zero algebraic flag specifications; no moving discriminant, dual quotient, signed exponent or phase.',
 half_laurent_cutoff=L,exact_phi_terms=T,exact_order_class_polynomials=HC,
 chosen_Witt_precision=29**6, calibration_flags=out),sort_keys=True,separators=(',',':')))
