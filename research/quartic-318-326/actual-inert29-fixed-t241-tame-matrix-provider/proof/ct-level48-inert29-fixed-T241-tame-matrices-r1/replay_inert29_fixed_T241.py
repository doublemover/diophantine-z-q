#!/usr/bin/env python3
"""All actual 241-isogeny arcs on the three fixed SS models, with E[16] / E[3] matrices."""
from pathlib import Path
from hashlib import sha256
from itertools import product
from functools import lru_cache
import os,sys,json,numpy as np
w=Path(__file__).resolve().parent.parent
s=w/'ct-level48-fixed103-D1751-conductor241-pilot-r1'
src=s/'check_fixed103_conductor241.py'
assert sha256((s/'SHA256SUMS').read_bytes()).hexdigest()=='5c90ea416b1adc1247849eaad96dd43c5ec5d3f83d8bb58c0568d3eb38f8eb92'
assert sha256(src.read_bytes()).hexdigest()==next(h for h,n in (line.split() for line in (s/'SHA256SUMS').read_text().splitlines()) if n==src.name)
S={'__file__':str(src),'__name__':'donor241','sys':sys}
exec(compile(src.read_bytes().split(b"if '--one' in sys.argv:")[0],str(src),'exec'),S)
globals().update({k:S[k] for k in ['g','m','c','F','F0','F4','P0','p','l','nonsq','fr','PH','trace4','lift4','small4','v_coeff','v_items','v_points','invs','jm','ja','key','labels','big','small_old','oldF2','EXPECTED','zp']})
POINTS=241
E=list(product(range(29),repeat=2))
A2=((-1%29,0),(0,0));ay=F0.sqrt(F0.c(20**3+1));assert ay is not None
A3=((20,0),F0.residue(ay))
tgt={0:((0,0),(1,0),[]),2:((14,0),(22,0),[A2]),25:((6,0),(21,0),[A3,(A3[0],F0.residue(F0.sc(ay,-1)))])}
Jkeys=list(tgt)
def ordp(x,l):
 e=0
 while x%l==0:e+=1;x//=l
 return e
def jdF(P,A,f):
 X,Y,Z=P
 if not f.nz(Z) or not f.nz(Y):return g.jp(None,f)
 u,v,w,s=f.su,f.ad,f.mu,f.sc
 xx=w(X,X);yy=w(Y,Y);cc=w(yy,yy)
 D=s(u(u(w(v(X,yy),v(X,yy)),xx),cc),2);E=v(s(xx,3),w(A,f.pw(Z,4)))
 xx=u(w(E,E),s(D,2));return xx,u(w(E,u(D,xx)),s(cc,8)),s(w(Y,Z),2)
def jaF(P,Q,A,f):
 X,Y,Z=P;U,V,W=Q
 if not f.nz(Z):return Q
 if not f.nz(W):return P
 m,a,u,s=f.mu,f.ad,f.su,f.sc
 z=m(Z,Z);w=m(W,W)
 x1=m(X,w);x2=m(U,z);y1=m(Y,m(W,w));y2=m(V,m(Z,z));h=u(x2,x1);r=u(y2,y1)
 if not f.nz(h):return jdF(P,A,f) if not f.nz(r) else g.jp(None,f)
 h2=m(h,h);h3=m(h2,h);v=m(x1,h2);x=u(u(m(r,r),h3),s(v,2))
 return x,u(m(r,u(v,x)),m(y1,h3)),m(m(Z,W),h)
def jmF(P,k,A,f):
 O=g.jp(None,f)
 while k:
  if k&1:O=jaF(O,P,A,f)
  P=jdF(P,A,f);k//=2
 return O
def batch(L,f):
 D=[v[2] for v in L];acc=f.one;pref=[]
 for z in D:
  pref.append(acc)
  if f.nz(z):acc=f.mu(acc,z)
 rinv=f.inv(acc);ans=[]
 for (x,y,z),t in zip(reversed(L),reversed(pref)):
  if not f.nz(z):ans.append(None);continue
  zz=f.mu(rinv,t);rinv=f.mu(rinv,z);z2=f.pw(zz,2)
  ans.append((f.mu(x,z2),f.mu(y,f.mu(z2,zz))))
 return ans[::-1]
def fk(P):return None if P is None else key(P)
def basis(A,B,N,f):
 nn=abs((-p)**f.m-1);ell=2 if N==16 else 3
 assert ordp(nn,ell)==ordp(N,ell)
 aa=f.c(*A);bb=f.c(*B);BAS=[];H=set()
 for i in range(200):
  x=f.c(i%p,i//p)
  if f.m>1:x[0,1]=1
  y=f.sqrt(f.ad(f.ad(f.pw(x,3),f.mu(aa,x)),bb))
  if y is None:continue
  P=jmF(g.jp((x,y),f),nn//N,aa,f)
  R=jmF(P,N//ell,aa,f)
  if not f.nz(R[2]) or fk(g.jaff(R,f)) in H:continue
  assert not f.nz(jmF(P,N,aa,f)[2])
  BAS.append(P)
  if len(BAS)==2:return BAS
  H={fk(g.jaff(jmF(R,k,aa,f),f)) for k in range(ell)}
 raise ValueError(('no basis',A,B,N))
@lru_cache(None)
def frames(j):
 A,B,K=tgt[j];T={}
 for N,f in [(16,F4),(3,F0)]:
  P,Q=basis(A,B,N,f);z=f.c(*A)
  pairs=list(product(range(N),repeat=2))
  a=[jmF(P,i,z,f) for i in range(N)];b=[jmF(Q,i,z,f) for i in range(N)]
  Ps=batch([jaF(a[i],b[k],z,f) for i,k in pairs],f)
  tbl=dict(zip(pairs,Ps));d={fk(P):k for k,P in tbl.items()};assert len(d)==N*N
  T[N]=(tbl,d)
 return T
def label_matrix(j):
 A,B,K=tgt[j];F=frames(j)
 C16=[(1,t) for t in range(16)]+[(t,1) for t in range(0,16,2)]
 C3=[(1,t) for t in range(3)]+[(0,1)]
 return {(r,s):labels(A,B,F[16][0][r],tuple(F4.c(*a) for a in g.inbase(F[3][0][s],F0))) for r,s in product(C16,C3)}
iso={}
for j in Jkeys:
 A,B=tgt[j][:2]
 for u in E:
  if u==(0,0):continue
  AA=F0.bmul(A,F0.basepow(u,4));BB=F0.bmul(B,F0.basepow(u,6))
  # u maps A_j to (AA,BB); reserve u^{-1} for this inverse map.
  v=F0.basepow(u,839)
  q=(AA,BB)
  assert q not in iso or iso[q][0]==j
  iso.setdefault(q,(j,v))
def all_seeds(u,v,A):
 J,K=g.jp(u,F),g.jp(v,F);L=[]
 for k in [1,nonsq]:
  U,V=jm(J,k,A),jm(K,k,A)
  C=[U]
  for ii in range(1,l):C.append(ja(C[-1],V,A))
  L.extend(C+[V])
 P=batch(L,F)
 return list(zip([z[0] for z in P[:l+1]],[z[0] for z in P[l+1:]]))
def get_t(j):
 A,B,K=tgt[j];a0,b0=tgt[0][:2]
 return P0 if j==0 else tuple(g.velu(a0,b0,K,P,F) for P in P0)
def arc_table(j):
 A,B,K=tgt[j];aa=F.c(*A)
 u,v=get_t(j);T=frames(j)
 Ps=[T[16][0][(1,0)],T[16][0][(0,1)]]
 Ps +=[tuple(F4.c(*x) for x in g.inbase(T[3][0][k],F0)) for k in [(1,0),(0,1)]]
 R=all_seeds(u,v,aa);assert len(R)==242
 w=[v_items(A,B,vv) for vv in R]
 D=invs([F.su(lift4(P[0]),r) for ww in w for P in Ps for r,t,z in ww])
 out=[]
 for i,rr in enumerate(R):
  AA,BB=v_coeff(A,B,rr);j0,s=iso[(AA,BB)]
  fp=v_points(w[i],Ps,D[32*i:32*i+32])
  T0=frames(j0)
  u=F4.c(*F0.basepow(s,2));v=F4.c(*F0.basepow(s,3))
  def tr(P):return F4.mu(u,P[0]),F4.mu(v,P[1])
  zz=[tr(P) for P in fp]; a,b=[T0[16][1][fk(P)] for P in zz[:2]]
  c,d=[T0[3][1][fk(tuple(F0.c(*x) for x in g.inbase(P,F4)))] for P in zz[2:]]
  assert (a[0]*b[1]-a[1]*b[0])%2==1 and (c[0]*d[1]-c[1]*d[0])%3
  out.append([j0,a,b,c,d])
 if '--progress' in sys.argv: print('arc table',j,len(out),file=sys.stderr,flush=True)
 return out
if '--one' in sys.argv:
 j=int(sys.argv[sys.argv.index('--one')+1]);A=arc_table(j)
 print(json.dumps(dict(scope='one fixed T241 source',source=j,arcs=A),separators=(',',':'),sort_keys=True));raise SystemExit
# Use a single process for three small tame frames (already reused for every arc).
L={j:[[[*a],[*b],*H] for (a,b),H in label_matrix(j).items()] for j in Jkeys}
assert [len({tuple(tuple(z) for z in a[2:]) for a in L[j]}) for j in Jkeys]==[32,96,96]
W={j:arc_table(j) for j in Jkeys}
# Reference verification using only the precomputed arc matrices. Full x-only
# basis census at 241 identifies eigendirections, no moving division needed.
Rlat=[]
for k in range(60):
 v=[F0.basepow(F.d,7*k*j) for j in range(120)]
 Rlat.append(tuple(np.array(t,dtype=np.int64) for t in zip(*v)))
def frfast(x,i):
 a,b=Rlat[i];xx,yy=x
 return np.array([(xx*a+2*yy*b)%p,(xx*b+yy*a)%p],dtype=np.uint8)
def xp(x):return x.astype(np.uint8,copy=False).tobytes()
Tco=[(1,k) for k in range(l)]+[(0,1)]
def Torbit(j):
 A,B,K=tgt[j];u,v=get_t(j)
 R=all_seeds(u,v,F.c(*A))
 D={}
 for i,orb in enumerate(R):
  for x in orb:
   for k in range(60):
    w=xp(frfast(x,k));assert w not in D;D[w]=Tco[i]
 assert len(D)==(l*l-1)//2
 return D
def frame_apply(M,v,n):
 a,b=M;s,t=v;return tuple((s*a[i]+t*b[i])%n for i in (0,1))
def frame_norm(v,n):
 a,b=v
 if a%(2 if n==16 else 3):return (1,pow(a,-1,n)*b%n)
 assert b%(2 if n==16 else 3)
 return pow(b,-1,n)*a%n,1
def sym(n,e):return 0 if n%l==0 else 1 if pow(n%l,(l-1)//2,l)==1 else -1
Lmaps={j:label_matrix(j) for j in Jkeys}
Tm={j:Torbit(j) for j in Jkeys}
Hfile=Path(src).parent/'EXACT-FIXED103-CONDUCTOR241.json'
assert sha256(Hfile.read_bytes()).hexdigest()=='b5291674384bbbfbcc094e2df042ae6fd654d020e38e6cd809caca474fd99efa'
HH=json.loads(Hfile.read_bytes())['phase_histograms']
reduced_hist=[]
for i in range(48):
 wa,wb=m.words[i];A,B,P2,P3,R2,R3=m.locate(wa,wb)
 j,k0=iso[(A,B)];Tm0=Tm[j];u,v=big(wa,wb)
 lam2=F.c(*F0.basepow(k0,2))
 a,b=[Tm0[xp(F.mu(lam2,P[0]))] for P in (u,v)]
 di=(a[0]*b[1]-a[1]*b[0])%l;assert di
 P=tuple(small_old(x) for x in g.amul(P2[0],2**(R2[0]-4),oldF2.c(*A),oldF2))
 Q=tuple(F0.c(*x) for x in g.inbase(g.amul(P3[0],3**(R3[0]-1),m.F3.c(*A),m.F3),m.F3))
 SS=frames(j);st=[]
 for X,f,N in [(P,F4,16),(Q,F0,3)]:
  z=(f.mu(f.c(*F0.basepow(k0,2)),X[0]),f.mu(f.c(*F0.basepow(k0,3)),X[1]))
  st.append(frame_norm(SS[N][1][fk(z)],N))
 assert Lmaps[j][tuple(st)]==tuple(tuple(v) for v in EXPECTED[i][5:7])
 H=[[0]*9,[0]*9]
 for z,arc in zip(Tco,W[j]):
  # det(z,W z)=det(S)*(r2-r1)*coordinates z in the two eigendirections.
  r=(z[0]*b[1]-z[1]*b[0])*pow(di,-1,l)%l
  s=(a[0]*z[1]-a[1]*z[0])*pow(di,-1,l)%l
  sign=sym(di*30*r*s,l)*sym(30,l)
  if not sign:continue
  j0,a1,b1,c1,d1=arc
  C16=frame_norm(frame_apply([a1,b1],st[0],16),16)
  C3=frame_norm(frame_apply([c1,d1],st[1],3),3)
  H[int(sign!=1)][PH[Lmaps[j0][C16,C3]]]+=1
 assert H==HH[i],(i,H,HH[i])
 reduced_hist.append(H)
 if '--progress' in sys.argv: print('reference',i,file=sys.stderr,flush=True)
exp=sum(k*(row[0][k]-row[1][k]) for row in reduced_hist for k in range(9))
assert exp==-86
print(json.dumps(dict(scope='three fixed T241 finite models only; no moving discriminant',
 phase_generator=[14,[0,13]],kernel_order='(1,k) k=0..240 followed by (0,1)',
 flags=L,arcs=W,reference_indices_checked=len(reduced_hist),reference_exact_exponent=exp),separators=(',',':'),sort_keys=True))
