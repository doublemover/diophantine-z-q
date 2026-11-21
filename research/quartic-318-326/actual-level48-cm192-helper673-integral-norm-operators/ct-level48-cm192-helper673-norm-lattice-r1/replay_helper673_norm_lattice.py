#!/usr/bin/env python3
"""From one true saturated quaternion order to all exact framed Hecke rows."""
import json,sys,os,time
from collections import Counter
from fractions import Fraction as F
from math import gcd,isqrt,lcm
from pathlib import Path
from hashlib import sha256
R=Path(__file__).resolve().parent.parent
def loaded(dir,pattern):
 branch={
  "EXACT-HELPER673-QUATERNION-SEED.json":"8e4570dc83493768278fb775626356966a1b10f7f29ec82fab3c6548037e5501",
  "EXACT-HELPER673-FRAMED-T17.json":"2745f5eceb36ad4d40b40e113433cf4da673893f107c538260f616c7d03fa4b1",
  "EXACT-HELPER673-FRAMED-T337.json":"798c876962373d4b874b23a5ac3434636ed0579a52f54dd1822b96141d5dd82a",
  "EXACT-HELPER673-FRAMED-T13.json":"e3b9fd0133abd21407ac787f9fb2294fd10740db1425c88fd5bc6f2ccac71fd5"}
 raw=(R/dir/pattern).read_bytes()
 assert sha256(raw).hexdigest()==branch[pattern]
 return json.loads(raw)
seed=loaded('ct-level48-cm192-helper673-quaternion-seed-r1','EXACT-HELPER673-QUATERNION-SEED.json')
T17=loaded('ct-level48-cm192-helper673-framed-t17-r1','EXACT-HELPER673-FRAMED-T17.json')
T337=loaded('ct-level48-cm192-helper673-framed-t337-r1','EXACT-HELPER673-FRAMED-T337.json')['T337']
r=337;m=r*r;p=673
unit=[[1,0],[0,1]]
unit4=[[int(i==j) for j in range(4)] for i in range(4)]
def mm(A,B,L=None):
 return [[sum(a*b for a,b in zip(x,y)) if L is None else sum(a*b for a,b in zip(x,y))%L for y in zip(*B)] for x in A]
def inv2(A,L=None):
 (a,b),(c,d)=A
 if L is None:
  assert abs(a*d-b*c)==1
  e=a*d-b*c
 else:e=pow(a*d-b*c,-1,L)
 return [[d*e,-b*e],[-c*e,a*e]]
def scale(A,c,L):
 return [[c*z%L for z in row] for row in A]
def combine(cs, As, L):
 return [[sum(c*A[i][j] for c,A in zip(cs,As))%L for j in range(2)] for i in range(2)]
def mats(OM,PI,L):
 OP=mm(PI,OM,L)
 t=combine([3,-6,-1,2],[unit,OM,PI,OP],L)
 return [unit,OM,OP,scale(t,pow(11,-1,L),L)]
a,b=seed['pi_337_multiplier']
num=a*a+a*b+3*b*b+p
assert num%r==0
a+=r*((-(num//r))*pow(2*a+b,-1,r)%r)
assert (a*a+a*b+3*b*b+p)%m==0
om=[[0,1],[-3,1]]
pi=[[a,b],[a+3*b,-a]]
ones=combine([1],[unit],m)
assert mm(om,om,m)==combine([-3,1],[unit,om],m)
assert mm(pi,pi,m)==scale(unit,-p,m)
assert combine([1,1],[mm(om,pi,m),mm(pi,om,m)],m)==scale(pi,1,m)
ams=mats(om,pi,m)
a0=T337['0']
qi,qi1=seed['q337_in_p_omega']
xs=[];ts=[];si=[]
for i in range(56):
 if i==0:
  xs.append(unit);ts.append(1);si.append(unit+unit)
  continue
 j=next(j for j,(v,_) in enumerate(a0) if v==i)
 x,y=((1+j*qi)%r,j*qi1%r) if j<r else (qi,qi1)
 B=[[1,y*pow(x,-1,r)%r],[0,1]] if x else [[0,1],[-1,0]]
 xs.append(B);ts.append(r);si.append(a0[j][1])

def rational_order(a):
 # u=(2w-1)(pi-3)/11=(3-6w-pi+2w*pi)/11.
 x,y,z,t=a
 return 11*x+3*t,11*y-6*t,-t,11*z+2*t
def bil(x,y):
 a,b,c,d=rational_order(x);u,v,w,t=rational_order(y)
 return 2*a*u+a*v+b*u+6*b*v+p*(2*c*w+c*t+d*w+6*d*t)
def gram(B):
 G=[[bil(u,v) for u in B] for v in B]
 mu=[[F(0) for _ in B] for _ in B]
 g=[]
 for i in range(4):
  for j in range(i):
   s=F(G[i][j])-sum(mu[i][k]*mu[j][k]*g[k] for k in range(j))
   mu[i][j]=s/g[j]
  g.append(F(G[i][i])-sum(mu[i][k]**2*g[k] for k in range(i)))
 return mu,g
def lll(B):
 k=1;mu,g=gram(B)
 while k<4:
  for j in range(k-1,-1,-1):
   a=round(mu[k][j])
   if a:
    B[k]=[x-a*y for x,y in zip(B[k],B[j])]
    for i in range(j):mu[k][i]-=a*mu[j][i]
    mu[k][j]-=a
  if g[k]>=(F(3,4)-mu[k][k-1]**2)*g[k-1]:
   k+=1
  else:
   B[k],B[k-1]=B[k-1],B[k];mu,g=gram(B);k=max(k-1,1)
 assert all(g0>0 for g0 in g)
 return B,mu,g
def divisible(B,cs,M):
 ds=[sum(a*b for a,b in zip(v,cs))%M for v in B]
 z=gcd(M,*ds)
 if z==M:return B
 M//=z;ds=[d//z for d in ds]
 j=next(j for j,d in enumerate(ds) if gcd(d,M)==1)
 rr=pow(ds[j],-1,M);p=B[j]
 for k in range(4):
  if k!=j:
   t=-ds[k]*rr%M
   if 2*t>M:t-=M
   B[k]=[x+t*y for x,y in zip(B[k],p)]
 B[j]=[M*x for x in p]
 return B

def hom(i,j):
 if not (i or j):return lll([v[:] for v in unit4])
 U=xs[i]; V=inv2(xs[j])
 T=[mm(mm(U,M,m),V,m) for M in ams]
 B=[v[:] for v in unit4]
 for x,y,R0 in ((0,0,ts[i]),(0,1,ts[i]*ts[j]),(1,1,ts[j])):
  if R0>1:B=divisible(B,[M[x][y]%R0 for M in T],R0)
 assert all(sum(c*M[x][y] for c,M in zip(v,T))%R0==0
    for v in B for x,y,R0 in ((0,0,ts[i]),(0,1,ts[i]*ts[j]),(1,1,ts[j])))
 return lll(B)

def enum_prep(mu,g,den):
 GG=[]
 for i in range(4):
  if i:
   B=[[sum((g[k]*mu[j][k]*mu[h][k] for k in range(i,min(j,h))),F(0))
        + (g[min(j,h)] if j==h else g[min(j,h)]*mu[max(j,h)][min(j,h)]) for h in range(i,4)] for j in range(i,4)]
  else:
   B=[[sum((g[k]*mu[j][k]*mu[h][k] for k in range(min(j,h))),F(0))
        + (g[min(j,h)] if j==h else g[min(j,h)]*mu[max(j,h)][min(j,h)]) for h in range(4)] for j in range(4)]
  B=[[x/den for x in row] for row in B]
  L=lcm(*(z.denominator for row in B for z in row))
  eq=[[int(z*L) for z in row] for row in B]
  GG.append((L,eq))
 assert GG[0][0]==1
 return GG

def enumerate_norm(B,GG,R0):
 (l0,g0),(l1,g1),(l2,g2),(l3,g3)=GG
 cap3=isqrt(l3*R0//g3[0][0])
 lin2=g2[0][1]; a2=g2[0][0]; c2=g2[1][1]
 a1=g1[0][0]; l12,l13=g1[0][1:];c11=g1[1][1];c12=g1[1][2];c22=g1[2][2]
 a0=g0[0][0];l01,l02,l03=g0[0][1:];aa0=g0[1][1];ab0,ac0=g0[1][2:];bb0=g0[2][2];bc0=g0[2][3];cc0=g0[3][3]
 for z in range(cap3+1):
  cz=l2*R0-c2*z*z; bz=lin2*z
  dd2=bz*bz+a2*cz
  if dd2<0:continue
  iz=isqrt(dd2)
  ymin=(-iz-bz+a2-1)//a2
  for y in range(ymin if z else max(ymin,0),(iz-bz)//a2+1):
   c1=l1*R0-c11*y*y-2*c12*y*z-c22*z*z
   b1=l12*y+l13*z
   d1=b1*b1+a1*c1
   if d1<0:continue
   z1=isqrt(d1)
   lo1=(-z1-b1+a1-1)//a1
   bc=l02*y+l03*z
   bet=2*(ab0*y+ac0*z)
   g0a=R0-bb0*y*y-2*bc0*y*z-cc0*z*z
   for x in range(lo1 if y or z else max(lo1,0),(z1-b1)//a1+1):
    b0=l01*x+bc
    d0=b0*b0+a0*(g0a-x*(aa0*x+bet))
    if d0<0:continue
    t=isqrt(d0)
    if t*t!=d0:continue
    for u in ([-t,t] if t else [0]):
     w0,w1=divmod(u-b0,a0)
     if w1 or w0<0 and not (x or y or z):continue
     kk=[w0,x,y,z]
     a=[sum(kk[j]*B[j][h] for j in range(4)) for h in range(4)]
     yield a

ss=[[],[]]
for L,n in ((32,0),(3,1)):
 oms=seed['omega_32_3'][2*n:2*n+2];psi=seed['pi_32_3'][2*n:2*n+2]
 so=mats(oms,psi,L)
 sf=[c[2*n:2*n+2] for c in si]
 ss[n]=[(L,so, mm(inv2(sf[i],L),unit,L),sf[i],pow(ts[i],-1,L)) for i in range(56)]
def deck(a,i,j):
 out=[]
 for s in ss:
  L,os,ii,_,_=s[i];_,_,_,jj,invj=s[j]
  M=combine(a,os,L);out+=scale(mm(mm(ii,M,L),jj,L),invj,L)
 return out

def row(i,ells):
 result={ell:[] for ell in ells}
 for j in range(56):
  B,mu,g=hom(i,j)
  den=121*ts[i]*ts[j];G=enum_prep(mu,g,den)
  for ell in ells:
   for a in enumerate_norm(B,G,2*ell):
    assert bil(a,a)==2*ell*den
    M=deck(a,i,j)
    result[ell].append([j,M])
 assert all(len(result[ell])==ell+1 for ell in ells),[(ell,len(result[ell])) for ell in ells]
 return result

def canon(edge):
 j,M=edge
 col=lambda a:tuple(w for v in a for w in v)
 return j,min(col(M),col(scale(M[:2],-1,32)+scale(M[2:],-1,3)))
def eqrow(a,b):
 return Counter(canon(row) for row in a)==Counter(canon(row) for row in b)
def task(i):
 z=row(i,ells)
 if 17 in z:assert eqrow(z[17],T17['T17'][i]),i
 if 337 in z:assert eqrow(z[337],T337[str(i)]),i
 if 13 in z:assert eqrow(z[13],T13[i]),i
 if '--progress' in sys.argv:print('done',i,'secs',round(time.time()-start,1),file=sys.stderr)
 return z

if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 import multiprocessing
 ells=[int(x) for x in sys.argv[1].split(',')] if len(sys.argv)>1 else [13,17,337]
 inds=[int(x) for x in sys.argv[2:] if x.isdigit()] or list(range(56))
 T13=loaded('ct-level48-cm192-helper673-framed-t13-r1','EXACT-HELPER673-FRAMED-T13.json')['T13']
 jobs=int(os.environ.get('REPLAY_JOBS','1'))
 start=time.time()
 if jobs==1:
  out={i:task(i) for i in inds}
 else:
  with ProcessPoolExecutor(max_workers=jobs,mp_context=multiprocessing.get_context('fork')) as pool:
   out=dict(zip(inds,pool.map(task,inds)))
 print(json.dumps(dict(scope='exact numerical reference operators, no selected product',p=p,ells=ells,rows=out),sort_keys=True,separators=(',',':')))
