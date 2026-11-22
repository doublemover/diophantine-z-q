#!/usr/bin/env python3
"""Exact D=-311 regular control: all 19 ordered base flags and 241 weighted fibers."""
from pathlib import Path
from hashlib import sha256
from functools import lru_cache
from math import isqrt,gcd
from itertools import product
import json,sys
root=Path(__file__).resolve().parent.parent
p0=root/'ct-level48-inert29-fixed-T241-tame-matrices-r1'
assert sha256((p0/'SHA256SUMS').read_bytes()).hexdigest()=='62a3ecd69c5e9fc706e52c921cc1e55ba76bdfb5412a83c47ea9e9a03b95f26e'
for ln in (p0/'SHA256SUMS').read_text().splitlines():
 h,n=ln.split();assert sha256((p0/n).read_bytes()).hexdigest()==h
T=json.loads((p0/'EXACT-INERT29-FIXED-T241-MATRICES.json').read_text())
src=p0/'replay_inert29_fixed_T241.py'; b=src.read_bytes()
env={'__file__':str(src),'__name__':'T241_provider_only'}
exec(compile(b.split(b"\nif '--one' in sys.argv:")[0],str(src),'exec'),env)
R=b.split(b'Rlat=[]')[1].split(b'Lmaps={')[0]
exec(compile(b'Rlat=[]'+R,str(src),'exec'),env)
g,m,c,F,F0,F4,p,l,P0,PH,iso,frames,small_old,oldF2,Torbit,Tco,batch=(env[k] for k in 'g m c F F0 F4 p l P0 PH iso frames small_old oldF2 Torbit Tco batch'.split())
assert p==29 and l==241
D=-311;N=78;Q=lambda a,b:a*a-a*b+b*b
sf=lambda v:all(v%(k*k) for k in range(2,isqrt(v)+1))
def leg(d,l):return 0 if d%l==0 else 1 if pow(d%l,(l-1)//2,l)==1 else -1
assert [n for n in range(23,-D+1,24) if sf(n) and [leg(-n,l) for l in (5,29,241)]==[1,-1,-1]]==[-D]
# alpha=(7+11omega+(1+5omega)pi)/3; the integral tau summand is (1-pi)(1+2omega)/3.
assert 2*7-11==3 and Q(7,11)+29*Q(1,5)==9*N
f0=F0
sqrtD=f0.residue(f0.sc(f0.ad(f0.one,f0.sc(f0.c(*g.ZETA),2)),11*pow(3,-1,29)))
assert sqrtD in ((0,2),(0,27))

def red(a,b,c):
 while True:
  h=(a-b)//(2*a);c+=h*b+h*h*a;b+=2*h*a
  if a>c:a,b,c=c,-b,a
  else:break
 if a==c or abs(b)==a:b=abs(b)
 return a,b,c
L=[(a,b,(b*b-D)//(4*a)) for a in range(1,isqrt(-D//3)+1) for b in range(-a+1,a+1)
   if (b*b-D)%(4*a)==0 and (b*b-D)//(4*a)>=a and(a!=(b*b-D)//(4*a) or b>=0) and gcd(a,b,(b*b-D)//(4*a))==1]
assert len(L)==19
IX={(1,1,N):0};bb=1
for i in range(1,20):
 if i>1:bb=next(z for z in (bb,bb+2**i) if (z*z-D)%2**(i+2)==0)
 row=red(2**i,bb,(bb*bb-D)//2**(i+2))
 if i<19:assert row not in IX;IX[row]=i
 else:assert row==(1,1,N)
assert set(IX)==set(L) and IX[(3,1,26)]==12
words={}
for a,b0 in product(range(-2,3),repeat=2):
 i=(a+12*b0)%19
 if i not in words or (abs(a)+abs(b0),a,b0)<(sum(map(abs,words[i])),*words[i]):words[i]=(a,b0)
assert len(words)==19

def neg(P,f):return P[0],f.sc(P[1],-1),P[2]
def omegaJ(P,f):return f.mu(f.c(*g.ZETA),P[0]),P[1],P[2]
def piJ(P,f):return tuple(f.pw(z,29) for z in P)
def S(P,f):
 A=g.ja(P,g.jmul(omegaJ(P,f),2,f),f)
 return g.ja(A,neg(piJ(A,f),f),f)
def aint(P,f):return g.ja(g.ja(g.jmul(P,2,f),g.jmul(omegaJ(P,f),3,f),f),omegaJ(piJ(P,f),f),f)
def alpha(P,f,n,divlift=None):
 T=g.jmul(S(P,f),pow(3,-1,n),f) if divlift is None else S(divlift,f)
 return g.ja(aint(P,f),T,f)
def eq(P,Q,f):
 A=g.jaff(P,f);B=g.jaff(Q,f)
 return (A is None and B is None) or (A is not None and B is not None and all(f.eq(z,w) for z,w in zip(A,B)))
def eig(ell,e,s,f):
 n=ell**e;h=s
 for k in range(1,e):h=next(h+j*ell**k for j in range(ell) if ((h+j*ell**k)**2-(h+j*ell**k)+N)%ell**(k+1)==0)
 nn=abs((-p)**f.m-1);ne=n if ell!=3 else 9*n
 assert nn%ne==0
 for i in range(200):
  x=f.c(i%p,i//p);x[0,1]=1
  y=f.sqrt(f.ad(f.pw(x,3),f.one))
  if y is None:continue
  C=g.jmul(g.jp((x,y),f),nn//ne,f)
  if ell==3:
   B=g.jmul(C,3,f);P=g.jmul(B,3,f)
   U=g.ja(alpha(B,f,3*n,C),g.jmul(B,h-1,f),f)
   R=g.ja(alpha(P,f,n,B),g.jmul(P,h-1,f),f)
   assert eq(g.jmul(U,3,f),R,f)
  else:
   U=None;P=C;R=g.ja(alpha(P,f,n),g.jmul(P,h-1,f),f)
  if not f.nz(g.jmul(R,n//ell,f)[2]):continue
  assert not f.nz(g.jmul(R,n,f)[2])
  assert eq(alpha(R,f,n,U),g.jmul(R,h,f),f)
  return g.jaff(R,f),h,i
 raise ValueError('no eigen generator')
e2=[eig(2,8,k,m.F2) for k in (0,1)];e3=[eig(3,3,k,m.F3) for k in (0,1)]
base=((0,0),(1,0),tuple(q[0] for q in e2),tuple(q[0] for q in e3),(8,8),(3,3))
@lru_cache(None)
def locate(a,b):
 if b:return m.move(locate(a,b-1 if b>0 else b+1),3,0 if b>0 else 1)
 if a:return m.move(locate(a-1 if a>0 else a+1,0),2,0 if a>0 else 1)
 return base
@lru_cache(None)
def big(a,b):
 if (a,b)==(0,0):return P0
 if b:
  s=0 if b>0 else 1;u=(a,b-1+2*s);r=3
 else:
  s=0 if a>0 else 1;u=(a-1+2*s,0);r=2
 M=locate(*u);K=env['S']['Ksmall'](M,r,s)
 return tuple(g.velu(M[0],M[1],K,P,F) for P in big(*u))

def det(u,v):return (u[0]*v[1]-u[1]*v[0])%l
def mv(M,v):return tuple((a*v[0]+b*v[1])%l for a,b in M)
def mm(M,N):return tuple(tuple(sum(M[i][k]*N[k][j] for k in (0,1))%l for j in (0,1)) for i in (0,1))
I=((1,0),(0,1))
def mat(*terms):return tuple(tuple(sum(c*M[i][j] for c,M in terms)%l for j in (0,1)) for i in (0,1))
def tr(M):return (M[0][0]+M[1][1])%l
def inv(M):
 d=pow(det(M[0],M[1]),-1,l)
 return ((d*M[1][1]%l,-d*M[0][1]%l),(-d*M[1][0]%l,d*M[0][0]%l))
def char(x):return 0 if x%l==0 else 1 if pow(x%l,(l-1)//2,l)==1 else -1

def bsgs(Targ,H):
 oo=g.jp(None,F);step=g.jmul(H,16,F);xs=[oo];ys=[Targ]
 for _ in range(15):xs.append(g.ja(xs[-1],H,F));ys.append(g.ja(ys[-1],neg(step,F),F))
 key=env['key'];H0={None if Q is None else key(Q):i for i,Q in enumerate(batch(xs,F))}
 ans=next((i*16+H0[k])%l for i,Q in enumerate(batch(ys,F)) if (k:=(None if Q is None else key(Q))) in H0)
 assert eq(Targ,g.jmul(H,ans,F),F)
 return ans
R0,R1=env['S']['r'];a=(R1-14)*pow((R0-R1)%l,-1,l)%l;d=(-1-a)%l
P,Q0=map(lambda v:g.jp(v,F),P0)
P1=g.ja(omegaJ(P,F),neg(g.jmul(P,a,F),F),F);cc=bsgs(P1,Q0);assert cc
bb=(a*d-1)*pow(cc,-1,l)%l
OM=((a,bb),(cc,d));assert eq(omegaJ(Q0,F),g.ja(g.jmul(P,bb,F),g.jmul(Q0,d,F),F),F)
PI=mm(inv(mat((4,I),(1,OM))),mat((1,((R0,0),(0,R1))),(-5,I),(-9,OM)))
assert mm(PI,PI)==mat((-29,I)) and mm(PI,OM)==mm(mm(OM,OM),PI)
for i,V0 in enumerate((P,Q0)):
 assert eq(piJ(V0,F),g.ja(g.jmul(P,PI[0][i],F),g.jmul(Q0,PI[1][i],F),F),F)
TA=mat((pow(3,-1,l),mm(mat((1,I),(-1,PI)),mat((1,I),(2,OM)))))
AL=mat((2,I),(3,OM),(1,mm(OM,PI)),(1,TA))
VD=mat((2,AL),(-1,I));assert tr(VD)==0 and mm(VD,VD)==mat((D,I))

def gz():
 # Miller evaluations with the common O-normalization. Inversion of the usual
 # Weil root convention has no effect on a quadratic Gauss sum at 241.
 def step(A,B,C):
  if A is None:return B,F.one
  if B is None:return A,F.one
  x,y=A;z,w=B;X,Y=C
  if F.eq(x,z) and not F.nz(F.ad(y,w)):return None,F.su(X,x)
  sl=F.di(F.sc(F.pw(x,2),3),F.sc(y,2)) if F.eq(x,z) else F.di(F.su(w,y),F.su(z,x))
  J=g.ap(A,B,F.zero,F)
  return J,F.di(F.su(F.su(Y,y),F.mu(sl,F.su(X,x))),F.su(X,J[0]))
 def mill(A,C):
  P=A;u=F.one
  for b in bin(l)[3:]:
   P,v=step(P,P,C);u=F.mu(F.pw(u,2),v)
   if b=='1':P,v=step(P,A,C);u=F.mu(u,v)
  assert P is None
  return u
 Z=F.sc(F.di(mill(P0[0],P0[1]),mill(P0[1],P0[0])),-1)
 assert F.eq(F.pw(Z,l),F.one) and not F.eq(Z,F.one)
 w=F.one;z=F.zero
 for i in range(1,l):
  w=F.mu(w,Z);z=F.ad(z,F.sc(w,char(i)))
 val=F.residue(z);assert val in ((3,0),(26,0));return val
Gf=gz();factor=1 if Gf==(3,0) else -1
if '--progress' in sys.argv:print('seed matrices and named Gauss',sqrtD,Gf,flush=True,file=sys.stderr)
lab={int(j):{(tuple(a),tuple(b)):((tuple(X),tuple(Y)),PH[(tuple(X),tuple(Y))]) for a,b,X,Y in R} for j,R in T['flags'].items()}
arcs={int(j):V for j,V in T['arcs'].items()}

def norm(v,n):
 a,b=v;r=2 if n==16 else 3
 return (1,pow(a,-1,n)*b%n) if a%r else (pow(b,-1,n)*a%n,1)
def framea(a,b,v,n):return tuple((a[i]*v[0]+b[i]*v[1])%n for i in (0,1))
@lru_cache(None)
def xy_lookup(j):return Torbit(j)
def xbytes(x):return x.astype('uint8',copy=False).tobytes()

rows=[]
for i in range(19):
 a,b=words[i];M=locate(a,b);A,B,P2,P3,R2,R3=M
 j,k0=iso[(A,B)];tm=xy_lookup(j);u,v=big(a,b);aa=F.c(*A)
 w=g.jaff(env['jaF'](g.jp(u,F),g.jp(v,F),aa,F),F)
 sc=F.c(*F0.basepow(k0,2));U,V,W=[tm[xbytes(F.mu(sc,z[0]))] for z in (u,v,w)]
 cs=-det(U,W)*pow(det(V,W),-1,l)%l;VV=tuple(cs*t%l for t in V);mm0=tuple(zip(U,VV));assert char(det(U,VV))==1
 DV=mm(mm(mm0,VD),inv(mm0))
 P=tuple(small_old(x) for x in g.amul(P2[0],2**(R2[0]-4),oldF2.c(*A),oldF2))
 QQ=tuple(F0.c(*x) for x in g.inbase(g.amul(P3[0],3**(R3[0]-1),m.F3.c(*A),m.F3),m.F3))
 info=frames(j);form=[]
 for X,f,n in [(P,F4,16),(QQ,F0,3)]:
  z=(f.mu(f.c(*F0.basepow(k0,2)),X[0]),f.mu(f.c(*F0.basepow(k0,3)),X[1]))
  form.append(norm(info[n][1][env['fk'](z)],n))
 et=m.t16(M);eu=m.t16(m.move(M,3,0));rows0=c.C[(et,eu)]
 assert len(rows0)==1 and lab[j][tuple(form)][0]==rows0[0]
 H=[[0]*9,[0]*9]
 for v,(j1,a0,a1,b0,b1) in zip(Tco,arcs[j]):
  sign=factor*char(det(v,mv(DV,v)));assert sign
  F1=norm(framea(a0,a1,form[0],16),16),norm(framea(b0,b1,form[1],3),3)
  phase=lab[j1][F1][1];H[sign<0][phase]+=1
 assert [sum(h) for h in H]==[121,121]
 z=sum(k*(H[0][k]-H[1][k]) for k in range(9));rows.append([i,a,b,j,*rows0[0],DV,H,z])
 if '--progress' in sys.argv:print(i,j,z,flush=True,file=sys.stderr)
tot=sum(r[-1] for r in rows);assert tot==101 and tot%9==2 and tot%3==2
print(json.dumps(dict(scope='smallest n regular fixed-241 D=-311 direct CM phase; not actual original detector or computed valuation',
 D=D,n=311*241,class_number=19,absolute_named_radicals={'sqrt_D':sqrtD,'sqrt_241':[3,0]},raw_frame_gauss=Gf,
 seed_matrices={'omega':OM,'pi':PI,'V':VD},seed_level_roots=[e2[0][1],e3[0][1]],
 exact_signed_sum=tot,mod9=tot%9,mod3=tot%3,base_rows=rows),sort_keys=True,separators=(',',':')))
