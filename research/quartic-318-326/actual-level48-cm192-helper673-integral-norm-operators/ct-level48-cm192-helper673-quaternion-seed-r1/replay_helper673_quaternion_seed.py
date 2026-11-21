#!/usr/bin/env python3
"""Normalized CM endomorphism and maximal-order saturation on the j=209 model."""
from pathlib import Path
import sys,random,json
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'ct-level48-cm192-helper673-framed-t337-r1'))
import replay_helper673_framed_t337 as b
m=b.mods[0]; p=b.p
assert m.j==209 and (m.A,m.B)==(132,88)

def af(P):return b.toA([P],4)[0]
def times(k,P):return af(b.JP(k,b.fromA(P),m.A))
def Jadd(*terms):
 r=None
 for k,P in terms:
  if k<0:k=-k;P=(P[0],b.neg(P[1])) if P else None
  r=b.JA(r,b.JP(k,b.fromA(P),m.A),m.A)
 return af(r)
def Pi(P):return tuple(b.fr(x) for x in P) if P else None

def endo_candidates():
 for a,cc in ((190,88),(-190,-66)):
  dr=b.sqroot((a*a-4*cc)%p,2)
  assert dr is not None
  for r in [b.scl(pow(2,-1,p),b.add(-a%p,dr)),b.scl(pow(2,-1,p),b.sub(-a%p,dr))]:
   g1=b.add(b.scl(3,b.sq(r)),m.A);g2=b.add(b.add(b.scl(5,b.fmul(b.sq(r),r)),b.scl(3,b.fmul(r,m.A))),b.scl(2,m.B))
   A,B=b.sub(m.A,b.scl(10,g1)),b.sub(m.B,b.scl(14,g2));j=b.cal_j(A,B)
   if j!=m.j:continue
   u2=b.div(b.div(B,m.B,2),b.div(A,m.A,2),2)
   u=b.sqroot(u2,2)
   assert u and b.scl(132,b.sq(u2))==A and b.scl(88,b.fmul(b.sq(u2),u2))==B
   for u in (u,b.neg(u)):
    def om(P):
     if P is None or P[0]==r:return None
     x,y=P; z=b.inv(b.sub(x,r),4);g1=b.add(b.scl(3,b.sq(r)),m.A);g0=b.add(b.fmul(r,b.add(b.sq(r),m.A)),m.B)
     g=b.scl(4,b.fmul(g0,z));h=b.scl(2,g1);x0=b.add(x,b.fmul(b.add(h,g),z))
     dy=b.sub(1,b.fmul(b.add(h,b.scl(2,g)),b.sq(z)))
     return b.div(x0,u2,4),b.div(b.fmul(y,dy),b.fmul(u,u2),4)
    if all(Jadd((1,om(om(P))),(-1,om(P)),(3,P)) is None for P in m.q[:2]):
     yield r,u2,u

r,u2,u=next(endo_candidates())
def Om(P):
 if P is None or P[0]==r:return None
 x,y=P;z=b.inv(b.sub(x,r),4);g1=b.add(b.scl(3,b.sq(r)),m.A);g0=b.add(b.fmul(r,b.add(b.sq(r),m.A)),m.B)
 g=b.scl(4,b.fmul(g0,z));h=b.scl(2,g1);x0=b.add(x,b.fmul(b.add(h,g),z));dy=b.sub(1,b.fmul(b.add(h,b.scl(2,g)),b.sq(z)))
 return b.div(x0,u2,4),b.div(b.fmul(y,dy),b.fmul(u,u2),4)
for P in m.q:
 assert b.curve(Om(P),m.A,m.B)
 assert Jadd((1,Om(Om(P))),(-1,Om(P)),(3,P)) is None
# Write the chosen Fp2 coordinate against s^2=-11 for transfer to Fp5(s).
s=b.sqroot((-11)%p,2)
def pair(a):
 assert b.small(a,2) and b.small(s,2)
 return a%b.step_t, ((a>>(2*b.w))%b.step_t)*pow((s>>(2*b.w))%b.step_t,-1,p)%p
assert all(pair(K)[1]!=0 for K in (s,r))

# Actual 11-primary factorization witness uses Fp5 and x-map only.
# In Fp5, π has eigenvalue 3 on E[11], since 3^5=1 and (-3)^5=-1.
src=b.raw.decode();src=src[:src.index('# Supersingular j via')].replace('n=32','n=5')
x=src.index('c=pow');y=src.index('def scl',x)
src=src[:x]+'''c=1

def norm(a):return sum(((a>>(w*i))&mask)%p<<(w*i) for i in range(n))
def add(a,b):return norm(a+b)
def sub(a,b):return norm(a+ALLp-b)
def neg(a):return sub(0,a)
def fmul(a,b):
 q=a*b
 A=[(q>>(w*i))&mask for i in range(9)]
 for i in range(8,4,-1): A[i-4]+=A[i];A[i-5]-=2*A[i]
 return sum((A[i]%p)<<(w*i) for i in range(5))
'''+src[y:]
src=src.replace('assert ex(step_t,32)==c','').replace('assert a\n if a<p','assert a\n if a<p').replace('deg=32','deg=5')
src=src.replace(' z=1<<(w*(n//deg)) if deg>1 else c',' z=5\n assert ex(z,(ff-1)//2)==p-1')
ff={};exec(src,ff)
G=lambda f,*args:ff[f](*args)
# X^5-X+2 is irreducible iff X^{p^5}=X and no Fp zero.
assert G('ex',b.step_t,p**5)==b.step_t
assert all((x**5-x+2)%p for x in range(p))
assert pow(5,(p-1)//2,p)==p-1

def aa(x,y):return tuple(G('add',a,b0) for a,b0 in zip(x,y))
def ss(x,y):return tuple(G('sub',a,b0) for a,b0 in zip(x,y))
def mm(x,y):return G('sub',G('fmul',x[0],y[0]),G('scl',11,G('fmul',x[1],y[1]))),G('add',G('fmul',x[0],y[1]),G('fmul',x[1],y[0]))
assert (p**5+1)%121!=0
RNG=random.Random(67311)
for _ in range(120):
 x=sum(RNG.randrange(p)<<(b.w*k) for k in range(5)); y=G('sqroot',G('add',G('fmul',x,G('add',G('sq',x),132)),88),5)
 if y is None:continue
 P5=G('JP',(p**5+1)//11,(x,y,1),132)
 if P5:break
else:raise ValueError('11-entropy')
assert G('JP',11,P5,132) is None
p5,p6=G('toA',[P5,G('JP',6,P5,132)],5)
RR=pair(r); U2=pair(u2); g1=pair(b.scl(2,b.add(b.scl(3,b.sq(r)),m.A)));g0=pair(b.scl(4,b.add(b.fmul(r,b.add(b.sq(r),m.A)),m.B)))
y=ss((p5[0],0),RR)
assert y!=(0,0)
# Equality tests v(P5)=0: ω(P5)=±6P5, with the minus impossible by the verified ω polynomial.
test=aa(mm(ss((p5[0],0),mm(U2,(p6[0],0))),mm(y,y)),aa(mm(g1,y),g0))
sign=-3 if test==(0,0) else 3
# Saturating generator is (2ω-1)(π-sign)/11; it is primitive in the old lattice modulo 11.
assert sign in (3,-3)

def matrix_for(f):return b.coef([f(P) for P in m.q],m)
PI=matrix_for(Pi); OM=matrix_for(Om)

b.RNG=random.Random(673337)
P,Q=b.basis(m);PP=af(P);W=Om(PP)
assert W not in (None,PP) and Jadd((1,Om(W)),(-1,W),(3,PP)) is None
# Verify combined torsion points give an endomorphism identity by total degree <32²*337².
assert all(Jadd((1,Om(Pi(T))),(1,Pi(Om(T))),(-1,Pi(T))) is None for T in m.q[:2]+[PP,W])
assert all(Jadd((1,Pi(Pi(T))),(673,T)) is None for T in m.q[:2]+[PP,W])
assert pow(-11%337,168,337)==336

def logs(P,W,S):
 cur=None; dd={}
 for k in range(337):dd[af(cur)]=k;cur=b.JA(cur,b.fromA(P),m.A)
 assert len(dd)==337
 D=b.fromA((W[0],b.neg(W[1])));SS=b.fromA(S)
 vv=[SS]
 for k in range(1,337):vv.append(b.JA(vv[-1],D,m.A))
 hits=[(dd[x],i) for i,x in enumerate(b.toA(vv,4)) if x in dd]
 assert len(hits)==1
 return hits[0]

# Coordinates of older fixed 337 basis in (P,ωP), and π(P)=a+bω.
QP=logs(PP,W,af(Q));PIPI=logs(PP,W,Pi(PP))
assert (PIPI[0]**2+PIPI[0]*PIPI[1]+3*PIPI[1]**2+673)%337==0
assert QP[1]!=0
if __name__=='__main__':
 print(json.dumps(dict(p=p,curve=[132,88],omega_kernel_x=b.enc(r),omega_u=b.enc(u),omega_u2=b.enc(u2),omega_32_3=OM,pi_32_3=PI,prime11_saturation_pi_eigen=sign,norm_quotient_11=(673+sign**2)//11,
   exact_P5=[[(x>>(b.w*i))%b.step_t for i in range(5)] for x in p5],p5_omega_x_equal_times6=test==(0,0),q337_in_p_omega=QP,pi_337_multiplier=PIPI),sort_keys=True,separators=(',',':')))
