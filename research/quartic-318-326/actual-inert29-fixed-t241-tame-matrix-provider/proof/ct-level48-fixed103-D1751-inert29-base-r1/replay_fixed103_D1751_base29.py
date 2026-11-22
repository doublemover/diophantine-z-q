#!/usr/bin/env python3
"""Actual fixed K(-1751), 48 oriented maximal-order CM base labels in characteristic 29."""
from pathlib import Path
from hashlib import sha256
from math import isqrt,gcd
from functools import lru_cache
import json,sys,os
old=Path(__file__).resolve().parent.parent/'ct-level48-inert-oriented-cm-D119-pilot-r1'
assert sha256((old/'pilot_ladder.py').read_bytes()).hexdigest()=='cd8891aeb2c139fd03f199b1c1484147b12d8aaa0a50c9b835ae0257fa5a8130'
assert sha256((old/'replay_inert_cm_pilot.py').read_bytes()).hexdigest()=='870d52cf4a531cf44a25479a8ca8c9a33598e8758c25bb37579edf2a0c5d31eb'
sys.path.insert(0,str(old))
import pilot_ladder as g
import replay_inert_cm_pilot as y
import numpy as np
p=29;D=-1751
assert y.p==p
F0=g.F0;F2=g.F2;F3=g.F(81);g.F3=F3
assert F2.basepow(F2.d,8)==(1,0) and F2.basepow(F2.d,4)!=(1,0)
assert F3.basepow(F3.d,3)==(1,0) and F3.d!=(1,0)
assert pow(p*p,64,512)==1 and pow(p*p,32,512)!=1
assert pow(p*p,81,243)==1 and pow(p*p,27,243)!=1
assert pow(D%p,(p-1)//2,p)==p-1
assert sum(v*v%p==(x**3+1)%p for x in range(p) for v in range(p))+1==30

def red(a,b,c):
 while True:
  q=(a-b)//(2*a)
  c+=q*b+q*q*a;b+=2*q*a
  assert b*b-4*a*c==D
  if c<a:a,b,c=c,-b,a
  else:break
 if (abs(b)==a or a==c) and b<0:b=-b
 return a,b,c
def forms():
 L=[]
 for a in range(1,isqrt((-D)//3)+1):
  for b in range(-a,a+1):
   if (b*b-D)%(4*a):continue
   c=(b*b-D)//(4*a)
   if a<=c and gcd(a,b,c)==1 and ((abs(b)!=a and a!=c) or b>=0):L.append((a,b,c))
 return L
FR=forms();idx={(1,1,438):0}
b=3
for k in range(1,49):
 if k>1:b=next(b0 for i in range(5) if ((b0:=b+2*5**(k-1)*i)**2-D)%(4*5**k)==0)
 ff=red(5**k,b,(b*b-D)//(4*5**k))
 if k==48:assert ff==(1,1,438)
 else:assert ff not in idx;idx[ff]=k
assert set(idx)==set(FR) and len(FR)==48
i2=idx[(2,1,219)];i3=idx[(3,1,146)]
assert (i2,i3)==(4,27)
words={}
for a in range(-4,5):
 for b in range(-4,5):
  k=(i2*a+i3*b)%48
  if k not in words or (abs(a)+abs(b),a,b)<(abs(words[k][0])+abs(words[k][1]),*words[k]):words[k]=(a,b)
assert len(words)==48

def omega(P,f):
 X,Y=P
 I=g.jp(P,f)
 z=f.c(*g.ZETA)
 T=g.jp((f.mu(z,X),Y),f)
 x,y=f.pw(X,p),f.pw(Y,p)
 J=g.jp((x,y),f);U=g.jp((f.mu(z,x),y),f)
 return g.ja(g.ja(g.jmul(I,5,f),g.jmul(T,9,f),f),g.ja(g.jmul(J,4,f),U,f),f)
def negP(P,f):
 return P[0],f.sc(P[1],-1)
def eig(l,e,s,f):
 N=l**e
 r=s
 for j in range(1,e):
  r=next(a for i in range(l) if ((a:=r+i*l**j)**2-a+438)%(l**(j+1))==0)
 nn=abs((-p)**f.m-1);assert nn%N==0 and nn%(N*l)!=0
 for x0 in range(100):
  x=f.c(x0%p,x0//p);x[0,1]=1
  v=f.sqrt(f.ad(f.pw(x,3),f.one))
  if v is None:continue
  P=g.jaff(g.jmul(g.jp((x,v),f),nn//N,f),f)
  if P is None:continue
  Q=g.jaff(g.ja(omega(P,f),g.jmul(g.jp(P,f),(r-1)%N,f),f),f)
  if Q is None:continue
  J=g.jp(Q,f)
  if not f.nz(g.jmul(J,N//l,f)[2]):continue
  assert not f.nz(g.jmul(J,N,f)[2])
  W=g.jaff(omega(Q,f),f);V=g.jaff(g.jmul(J,r,f),f)
  assert (W is None and V is None) or (W is not None and V is not None and all(f.eq(x,y) for x,y in zip(W,V)))
  return Q,r,x0
 raise ValueError('no eigenspace generator')

g2=[eig(2,8,s,F2) for s in (1,0)]
g3=[eig(3,5,s,F3) for s in (1,0)]
p0=((0,0),(1,0),tuple(q[0] for q in g2),tuple(q[0] for q in g3),(8,8),(5,5))
# Check O_K eigenspace independence already on the two small primary quotients.
for l,e,gs,f in ((2,8,g2,F2),(3,5,g3,F3)):
 a,b=[g.jaff(g.jmul(g.jp(w[0],f),l**(e-1),f),f) for w in gs]
 ax=a[0];bx=b[0];assert not f.eq(ax,bx)
print('seed done',file=sys.stderr) if '--progress' in sys.argv else None

def move(M,l,d):
 A,B,P2,P3,R2,R3=M
 fs=F2 if l==2 else F3
 K0=P2 if l==2 else P3
 ee=R2 if l==2 else R3
 P=K0[d];e=ee[d]
 gen=g.inbase(g.amul(P,l**(e-1),fs.c(*A),fs),fs)
 K=[gen]
 if l==3:K.append((gen[0],F0.residue(F0.sc(F0.c(*gen[1]),-1))))
 AA,BB=F0.c(*A),F0.c(*B);a,b=AA,BB
 for x,v in K:
  X,Y=F0.c(*x),F0.c(*v)
  assert F0.eq(F0.pw(Y,2),F0.ad(F0.ad(F0.pw(X,3),F0.mu(AA,X)),BB))
  tv=F0.ad(F0.sc(F0.pw(X,2),3),AA)
  wv=F0.ad(F0.ad(F0.sc(F0.pw(X,3),5),F0.sc(F0.mu(AA,X),3)),F0.sc(BB,2))
  a=F0.su(a,F0.sc(tv,5));b=F0.su(b,F0.sc(wv,7))
 a,b=F0.residue(a),F0.residue(b)
 n2=tuple(g.velu(A,B,K,P,F2) for P in P2);n3=tuple(g.velu(A,B,K,P,F3) for P in P3)
 if l==2:R2=tuple(e-(k==d) for k,e in enumerate(R2))
 else:R3=tuple(e-(k==d) for k,e in enumerate(R3))
 for PP,RR,f,ell in ((n2,R2,F2,2),(n3,R3,F3,3)):
  for P,e in zip(PP,RR):
   if e==0:
    assert P is None
    continue
   assert P is not None
   X,Y=P
   assert f.eq(f.pw(Y,2),f.ad(f.ad(f.pw(X,3),f.mu(f.c(*a),X)),f.c(*b)))
 return (a,b,n2,n3,R2,R3)
@lru_cache(None)
def locate(a,b):
 if b:return move(locate(a,b-1 if b>0 else b+1),3,0 if b>0 else 1)
 if a:return move(locate(a-1 if a>0 else a+1,0),2,0 if a>0 else 1)
 return p0

def t16(M):
 A,B,P2,P3,R2,R3=M
 st=(A,B,P2[0],None); e=R2[0];T=[]
 for k in range(3):
  st,(q,q4)=g.step(*st,2,e-k)
  assert q4 is not None
  T.append(q4)
 vv=y.levels(y.levels(T,8),16)
 assert len(vv)==1
 return vv[0]

def one(i):
 a,b=words[i];M=locate(a,b);T=t16(M);U=t16(move(M,3,0));row=y.C.get((T,U),[])
 assert len(row)==1,(i,a,b,T,U,row)
 if '--progress' in sys.argv: print(i,flush=True,file=sys.stderr)
 return [i,a,b,T,U,*row[0]]
if __name__=='__main__' and int(os.environ.get('REPLAY_JOBS','1'))>1:
 from concurrent.futures import ProcessPoolExecutor
 import multiprocessing
 with ProcessPoolExecutor(max_workers=int(os.environ['REPLAY_JOBS']),mp_context=multiprocessing.get_context('fork')) as pool:
  calc=list(pool.map(one,range(48)))
else:calc=[one(i) for i in range(48)]
assert len(calc)==48
print(json.dumps(dict(p=p,D=D,class_number=len(FR),class_generator=5,classs_of_2=i2,classs_of_3=i3,
 counter_words=sorted(words.items()),marked_eigen_roots=[g2[0][1]%16,g3[0][1]%3],
 seed_roots={l:[(int(r),d) for Q,r,d in gg] for l,gg in ((2,g2),(3,g3))},
 marked_labels=calc,scope="48 fixed base class indices only; no conductor-weighted detector"),sort_keys=True,separators=(',',':')))
