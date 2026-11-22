#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
from types import SimpleNamespace
from itertools import product
from functools import lru_cache
import sys,os,json
import numpy as np
ROOT=Path(__file__).resolve().parent.parent
BASE=ROOT/'ct-level48-fixed103-D1751-inert29-base-r1'
path=BASE/'replay_fixed103_D1751_base29.py'
b=path.read_bytes()
assert sha256(b).hexdigest()=='449dd55839856b501b06b31c90186ea4301a9211df154a76f1d7d30bc9aead96'
pre=b.split(b"if __name__=='__main__' and int(os.environ")[0]
bb={'__file__':str(path),'__name__':'bound_fixed103_base'}
exec(compile(pre,str(path),'exec'),bb)
m=SimpleNamespace(**bb);g=m.g;c=m.y;F0=g.F0;oldF2=g.F2
p=29;q=p*p;l=241
E=list(product(range(p),repeat=2));a=next(u for u in E if all(F0.basepow(u,840//d)!=(1,0) for d in [2,3,5,7]) and u!=(0,0))
F=g.F(120);F.d=a
F4=g.F(4);F4.d=a
assert pow(-p,120,l)==1 and all(pow(-p,120//d,l)!=1 for d in [2,3,5]) and pow(-p,120,l*l)!=1
assert pow(-p,4,16)==1 and pow(-p,2,16)!=1 and pow(-p,1,3)==1
q4powers=[0,30,60,90]
Frob=[]
for k in range(4):
 v=[F0.basepow(a,7*k*j) for j in range(120)]
 Frob.append(tuple(np.array(t,dtype=np.int64) for t in zip(*v)))
def fr(x,i):
 s,t=Frob[i];xx,yy=x
 return np.array([(xx*s+2*yy*t)%p,(xx*t+yy*s)%p],dtype=np.int64)
def lift4(x):
 y=F.zero.copy();y[:,q4powers]=x;return y
def small4(x):
 assert not np.any(x[:,[i for i in range(120) if i%30]])
 return x[:,q4powers].copy()
def trace4(x):return x[:,q4powers].copy() # Tr(F120/F4)/30; 30=1 mod29
def comp4(x):
 return x[:,q4powers].copy()
def c4pow(t,n):return F4.pw(t,n)
i,h=next((i,h) for i in (1,3) for h in E if h!=(0,0) and F0.bmul(F0.basepow(h,4),F0.basepow(a,i))==oldF2.d)
T=F4.zero.copy();T[:,i]=h
emb=[c4pow(T,k) for k in range(4)]
def small_old(x):
 assert not np.any(x[:,[j for j in range(64) if j%16]])
 z=F4.zero.copy()
 for j in range(4):z=F4.ad(z,F4.mu(F4.c(*x[:,16*j]),emb[j]))
 return z
def Om(P):return m.omega(P,F)
r=[v for v in range(l) if (v*v-v+438)%l==0];assert len(r)==2
def jaff(P):return g.jaff(P,F)
def key(P):return tuple(tuple(map(int,x.flatten())) for x in P)
def mkseed():
 B=[None,None];N=abs((-p)**120-1)
 for i in range(100):
  x=F.c(i%p,i//p);x[0,1]=1
  y=F.sqrt(F.ad(F.pw(x,3),F.one))
  if y is None:continue
  J=g.jmul(g.jp((x,y),F),N//l,F)
  P=jaff(J)
  if P is None:continue
  assert jaff(g.jmul(J,l,F)) is None
  V=Om(P)
  for j in (0,1):
   if B[j] is not None:continue
   W=g.ja(V,g.jmul(J,(-r[1-j])%l,F),F)
   Q=jaff(W)
   if Q is None:continue
   assert key(jaff(Om(Q)))==key(jaff(g.jmul(W,r[j],F)))
   B[j]=Q
  if all(x is not None for x in B):return B
 raise ValueError('no l-eigenbasis')
P0=mkseed()
def Ksmall(M,l,s):
 A,B,P2,P3,R2,R3=M
 if l==2:f=oldF2;P=P2[s];e=R2[s]
 else:f=m.F3;P=P3[s];e=R3[s]
 Q=g.inbase(g.amul(P,l**(e-1),f.c(*A),f),f)
 return [Q] if l==2 else [Q,(Q[0],tuple(-v%p for v in Q[1]))]
@lru_cache(None)
def big(a,b):
 if (a,b)==(0,0):return P0
 if b:
  s=0 if b>0 else 1;u=(a,b-1+2*s);l0=3
 else:
  s=0 if a>0 else 1;u=(a-1+2*s,0);l0=2
 M=m.locate(*u);K=Ksmall(M,l0,s)
 return [g.velu(M[0],M[1],K,P,F) for P in big(*u)]
def jd(P,aa):
 X,Y,Z=P
 if not F.nz(Z) or not F.nz(Y):return g.jp(None,F)
 u,v,w,s=F.su,F.ad,F.mu,F.sc
 xx=w(X,X);yy=w(Y,Y);cc=w(yy,yy)
 D=s(u(u(w(v(X,yy),v(X,yy)),xx),cc),2);E=v(s(xx,3),w(aa,F.pw(Z,4)))
 x=u(w(E,E),s(D,2))
 return x,u(w(E,u(D,x)),s(cc,8)),s(w(Y,Z),2)
def ja(P,Q,aa):
 X,Y,Z=P;U,V,W=Q
 if not F.nz(Z):return Q
 if not F.nz(W):return P
 m,a,u,s=F.mu,F.ad,F.su,F.sc
 z=m(Z,Z);w=m(W,W)
 x1=m(X,w);x2=m(U,z);y1=m(Y,m(W,w));y2=m(V,m(Z,z));h=u(x2,x1);r=u(y2,y1)
 if not F.nz(h):return jd(P,aa) if not F.nz(r) else g.jp(None,F)
 h2=m(h,h);h3=m(h2,h);v=m(x1,h2);x=u(u(m(r,r),h3),s(v,2))
 return x,u(m(r,u(v,x)),m(y1,h3)),m(m(Z,W),h)
def jm(P,k,a):
 O=g.jp(None,F)
 while k:
  if k&1:O=ja(O,P,a)
  P=jd(P,a);k//=2
 return O
def invs(L):
 acc=F.one;pre=[]
 for x in L:
  assert F.nz(x)
  pre.append(acc);acc=F.mu(acc,x)
 cur=F.inv(acc);ret=[]
 for x,z in zip(reversed(L),reversed(pre)):
  ret.append(F.mu(cur,z));cur=F.mu(cur,x)
 return ret[::-1]
def bxs(L):
 return [F.mu(X,F.pw(z,2)) for (X,Y,Z),z in zip(L,invs([J[2] for J in L]))]
nonsq=next(x for x in range(1,l) if pow(x,(l-1)//2,l)==l-1)
def seeds(u,v,A):
 J,K=g.jp(u,F),g.jp(v,F);L=[]
 for k in [1,nonsq]:
  Jj,Kk=jm(J,k,A),jm(K,k,A)
  for ii in range(1,l):
   Jj=ja(Jj,Kk,A)
   L.append(Jj)
 ts=bxs(L);return list(zip(ts[:l-1],ts[l-1:]))
def v_coeff(A,B,rs):
 Ac,Bc=F4.c(*A),F4.c(*B);AA=F.c(*A);BB=F.c(*B)
 t=F.zero.copy();w=F.zero.copy()
 for r in rs:
  t=F.ad(t,F.ad(F.sc(F.pw(r,2),6),F.sc(AA,2)))
  w=F.ad(w,F.ad(F.ad(F.sc(F.pw(r,3),10),F.sc(F.mu(AA,r),6)),F.sc(BB,4)))
 assert F.eq(fr(t,2),F.pw(t,q*q)) if os.getenv('TRACE_ASSERT') else True
 return (F4.residue(F4.su(Ac,F4.sc(F4.c(*t[:,0]),5*60))), F4.residue(F4.su(Bc,F4.sc(F4.c(*w[:,0]),7*60))))
def v_items(A,B,rs):
 AA=F.c(*A);BB=F.c(*B)
 T=[]
 for r0 in rs:
  for i in range(4):
   r=fr(r0,i);r2=F.pw(r,2);t=F.ad(F.sc(r2,6),F.sc(AA,2));w=F.sc(F.ad(F.ad(F.mu(r,r2),F.mu(AA,r)),BB),4)
   T.append((r,t,w))
 return T
def v_points(R,Ps,L):
 out=[]
 for k,(x,y) in enumerate(Ps):
  s0=F4.zero.copy();s1=F4.zero.copy()
  for (r,t,w),u in zip(R,L[k*8:k*8+8]):
   v=F.mu(w,u);s0=F4.ad(s0,trace4(F.mu(F.ad(t,v),u)))
   s1=F4.ad(s1,trace4(F.mu(F.ad(t,F.sc(v,2)),F.pw(u,2))))
  out.append((F4.ad(x,F4.sc(s0,15)),F4.mu(y,F4.su(F4.one,F4.sc(s1,15)))))
 return out
def t16(A,B,P):
 old=g.F2;g.F2=F4
 try:
  z=(A,B,P,None);T=[]
  for k in range(3):
   z,(q,q4)=g.step(*z,2,4-k);assert q4 is not None
   T.append(q4)
  t=c.levels(c.levels(T,8),16);assert len(t)==1
  return t[0]
 finally:g.F2=old
def labels(A,B,P,Q):
 T=t16(A,B,P)
 q=g.inbase(Q,F4)
 K=[q,(q[0],tuple(-u%p for u in q[1]))]
 x=F0.c(*q[0]);a=F0.c(*A);b=F0.c(*B)
 a1=F0.residue(F0.su(a,F0.sc(F0.ad(F0.sc(F0.pw(x,2),3),a),10)))
 b1=F0.residue(F0.su(b,F0.sc(F0.ad(F0.ad(F0.sc(F0.pw(x,3),5),F0.sc(F0.mu(a,x),3)),F0.sc(b,2)),14)))
 U=t16(a1,b1,g.velu(A,B,K,P,F4))
 rr=c.C.get((T,U),[])
 assert len(rr)==1,(A,B,T,U)
 return rr[0]
aS=F0.c(*c.div(c.z(-13),c.z(3)));sx=c.div(c.z(2),c.z(3))
zG=g.lift((c.s((14,0),sx),(0,13)),F0)
def pp(P):return None if P is None else g.inbase(P,F0)
zp={pp(g.amul(zG,i,aS,F0)):i for i in range(9)}
assert len(zp)==9 and pp(g.amul(zG,9,aS,F0)) is None
def phase(X,Y):
 t=c.s(X,c.pw(X,839));w=c.div(Y,c.mu(X,X));xx=c.div(c.a(c.a(w,c.mu(t,t)),c.z(2)),c.z(2));yy=c.mu(t,xx)
 if not yy==(0,0) and xx==(0,0):raise ValueError('bad curve point')
 qq=g.lift((c.s(xx,sx),yy),F0);ff=g.lift((c.s(c.pw(xx,p),sx),c.pw(yy,p)),F0)
 return zp[pp(g.amul(g.ap(qq,(ff[0],F0.sc(ff[1],-1)),aS,F0),4,aS,F0))]
EXPECTED=json.loads((BASE/'EXACT-FIXED103-D1751-BASE29.json').read_bytes())['marked_labels']
PH={u:phase(*u) for a0 in c.C.values() for u in a0}
assert len(PH)>224
def one(i):
 a,b=m.words[i];M=m.locate(a,b);A,B=M[:2]
 u,v=big(a,b);g0=m.one(i);assert json.loads(json.dumps(g0))==EXPECTED[i]
 P=tuple(small_old(x) for x in g.amul(M[2][0],2**(M[4][0]-4),oldF2.c(*A),oldF2))
 Q=tuple(F4.c(*x) for x in g.inbase(g.amul(M[3][0],3**(M[5][0]-1),m.F3.c(*A),m.F3),m.F3))
 assert labels(A,B,P,Q)==tuple(g0[5:7])
 aa=F.c(*A)
 assert jaff(jm(g.jp(u,F),l,aa)) is None and jaff(jm(g.jp(v,F),l,aa)) is None
 ss=seeds(u,v,aa)
 Ps=[P,Q]
 R=[v_items(A,B,rs) for rs in ss]
 divs=invs([F.su(lift4(P[0]),r) for row in R for P in Ps for r,t,w in row])
 hist=[[0]*9,[0]*9]
 for k,rs in enumerate(ss,1):
  AA,BB=v_coeff(A,B,rs)
  p2,p3=v_points(R[k-1],Ps,divs[16*(k-1):16*k])
  for xx,yy in (p2,p3):
   assert F4.eq(F4.pw(yy,2),F4.ad(F4.ad(F4.pw(xx,3),F4.mu(F4.c(*AA),xx)),F4.c(*BB)))
  H=labels(AA,BB,p2,p3);s=pow(k,(l-1)//2,l)
  hist[int(s!=1)][PH[H]]+=1
 assert sum(hist[0])==sum(hist[1])==120
 if '--progress' in sys.argv: print(i,hist,flush=True,file=sys.stderr)
 return hist
if '--one' in sys.argv:
 calc=[one(int(sys.argv[sys.argv.index('--one')+1]))]
else:
 from concurrent.futures import ProcessPoolExecutor
 with ProcessPoolExecutor(max_workers=int(os.environ.get('REPLAY_JOBS','5'))) as pool:
  calc=list(pool.map(one,range(48)))
dest=sum(k*(h[0][k]-h[1][k]) for h in calc for k in range(9))%9
print(json.dumps({'scope':'fixed K0 primitive chi241 reference only; not selected full conductor','base_indices':len(calc),'binomial_constant':a,'seed_eigenvalues':r,'phase_histograms':calc,'phase_mod9_up_to_sign':dest},sort_keys=True,separators=(',',':')))
