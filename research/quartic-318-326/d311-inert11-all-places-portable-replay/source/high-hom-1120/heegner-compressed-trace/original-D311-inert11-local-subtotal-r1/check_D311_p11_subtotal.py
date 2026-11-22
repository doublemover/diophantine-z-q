from pathlib import Path
from hashlib import sha256
import json, math,random
from fractions import Fraction as F
import flint
ROOT=Path(__file__).resolve().parent.parents[2];H=ROOT/'high-hom-1120/heegner-compressed-trace'
P0=H/'original-inert29-exact-calibration-field-r1/EXACT-CALIBRATION-FIELD.json'
P1=H/'original-inert29-CM-real-ideal-r2/EXACT-REAL-CM-CUBIC.json'
assert sha256((P0.parent/'SHA256SUMS').read_bytes()).hexdigest()=='1f216d1caf9ac4b985132a984aaf191eb51467fa045d6012e3790e7bad0c24a7'
assert sha256((P1.parent/'SHA256SUMS').read_bytes()).hexdigest()=='c763e955648ab6ecc2873fdf2250e69478270cc6cf07a7b63d0c87f5aa528517'
for donor in (P0.parent,P1.parent):
 for line in (donor/'SHA256SUMS').read_text().splitlines():
  h,n=line.split(maxsplit=1)
  assert sha256((donor/n).read_bytes()).hexdigest()==h
D=json.loads(P0.read_text());P=json.loads(P1.read_text())
assert tuple(b for K,DD,A,pr in P['signed_whole_packets'] if K==5 and pr==1 for b in A if b in ([296,149],[600,593]))==([296,149],[600,593])

# Identify the literal characteristic-zero Cl-square mate by a nonbacktracking
# two-edge horizontal T7 path in the ordinary canonical reduction at 29.
C29=flint.fq_default_ctx(modulus=flint.fmpz_mod_poly_ctx(29)([-2,0,1]))
def g29(b):return tuple(C29(x%29)+(x//29)*C29.gen() for x in b)
def Hj(T):
 X,Y=T
 t=X-2+6*X/(Y+X**4+1)
 for a in (2,4,16):t=t*t/(t+a)
 return (t+256)**3/(t*t)
def jfr(T):
 X,Y=T
 return Hj(((X+1)/(X-1),4*Y/(X-1)**4))
def hg(T,S):
 def b(P):
  x,y=P; a=y+x**4
  return [1,a]+[x**k*(a+7) for k in range(1,5)]
 x,y=b(T),b(S)
 return 2+2*(x[5]+y[5])-2*x[1]*y[1]-x[2]*y[2]+2*x[3]*y[3]-x[4]*y[4]
d0=ROOT/'rc-native-helper-20261120/ct-level48-Kminus5-exact-calibration-lifts-r1'
assert sha256((d0/'SHA256SUMS').read_bytes()).hexdigest()==D['donor_manifest_sha256']
dd=d0/'EXACT-KMINUS5-CALIBRATION-LIFTS.json'
assert sha256(dd.read_bytes()).hexdigest()==D['donor_json_sha256']
def hpp(h,x):
 r=0
 for a in h:r=r*x+a
 return r
Hs=json.loads(dd.read_text())['exact_order_class_polynomials']
A0=g29((296,149));B0=g29((66,753));C0=g29((600,593))
assert len({Hj(x) for x in (A0,B0,C0)})==3
for T in (A0,B0,C0):
 X,Y=T;assert Y*Y==X**8+14*X**4+1
 assert hpp(Hs['4'],Hj(T))==0 and hpp(Hs['12'],jfr(T))==0
assert hg(A0,B0)==hg(B0,C0)==0
# 241-prime form (-D=2880). Completing the Euclidean proper reductions
# gives (16,16,49); the (same) inverse has order 2.
def reduce_form(a,b,c):
 while True:
  if abs(b)>a:
   q=(a-b)//(2*a);a,b,c=a,b+2*a*q,c+b*q+a*q*q
  if a>c:a,b,c=c,-b,a;continue
  if (abs(b)==a or a==c) and b<0:b=-b
  return (a,b,c)
assert {reduce_form(241,b,(b*b+2880)//964) for b in range(-241,242) if (b*b+2880)%964==0}=={(16,16,49)}
assert {reduce_form(49,b,(b*b+2880)//196) for b in range(-49,50) if (b*b+2880)%196==0}=={(16,16,49)}

p=11;poly=[2,0,0,0,1]+[0]*91+[1]
C=flint.fq_default_ctx(modulus=flint.fmpz_mod_poly_ctx(p)(poly))
sx=[0]*93
for e,v in ((92,6),(88,7),(80,7),(76,7),(68,8),(64,7),(60,7),(52,6),(44,7),(40,7),(36,5),(32,7),(28,4),(20,5),(16,10),(12,10),(8,5),(4,7),(0,3)):sx[e]=v
s=C(sx); i=4*s; a=s; z=5
assert s*s==2 and i*i==-C(1) and (a*a+2)**2==5 and C(z)**2==3
assert C(241)==i*i and (2*s)**2==-C(311) and (2*s)*i==5
def at(X,n):
 I=[(0,0),(0,2)]+[(k,j) for j in range(n//4) for k in range(4) if (k,j) not in ((0,0),(0,2))]
 return sum(C(v.numerator)/C(v.denominator)*a**k*i**(j&1)*s**(j>>1&1)*C(z)**(j>>2&1) for v,(k,j) in zip(map(F,X),I))
base=[C(u)+v*s for u in range(p) for v in range(p)]
e2=lambda x:next([u,v] for u in range(p) for v in range(p) if C(u)+v*s==x)
def chart(X,Y):
 B=(Y+X**4+1)/2
 if B==0 or X==0:return None
 return X-2+3*X/B,(B-2*X-1)/X
ff={tuple(x['flag']):x for x in D['exact_flags']}
FS=[]
for K,DD,A,pr in P['signed_whole_packets']:
 if K!=5:continue
 for b in A:
  f=ff[tuple(b)]; X,Y,J,JD=(at(x,f['dimensions']) for x in f['exact'])
  if J!=C(1728):continue
  c=chart(X,Y)
  if c is None:continue
  FS.append((b,X,Y,c,f['poly_source'],pr))
if not FS:raise SystemExit(0)
O=None;neg=lambda P:None if P is None else (P[0],-P[1])
def add(P,Q,A=-C(1)):
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u:
  if y!=v or y==0:return O
  m=(3*x*x+A)/(2*y)
 else:m=(v-y)/(u-x)
 w=m*m-x-u
 return w,m*(x-w)-y
def mu(k,P,A=-C(1)):
 if k<0:return mu(-k,neg(P),A)
 Q=O
 while k:
  if k&1:Q=add(Q,P,A)
  P=add(P,P,A);k//=2
 return Q
def velu(A,B,K):
 R,T=A,B
 for x,_ in K:
  R-=5*(3*x*x+A)
  T-=7*(5*x**3+3*A*x+2*B)
 def g(P):
  if P is None or P in K:return None
  x,y=P
  for U in K:
   Z=add(P,U,A)
   assert Z is not None
   x+=Z[0]-U[0];y+=Z[1]-U[1]
  assert y*y==x**3+R*x+T
  return x,y
 return R,T,g
def t8(P8,L):
 u=mu(4,P8,L)[0]
 b=3*u*u+L
 p=mu(2,P8,L)[0]-u
 v=P8[0]-u
 assert p*p==b
 return 32/((v+b/v)/p-6)
def t16(P,L,B):
 a0=t8(mu(2,P,L),L)
 R=mu(8,P,L)
 L2,B2,g=velu(L,B,[R])
 a1=t8(g(P),L2)
 t=[v for v in base if v!=-C(2) and v*v/(v+2)==a0 and v*(v+4)==a1]
 assert len(t)==1,(a0,a1)
 return t[0]
rng=random.Random(311)
def point():
 while True:
  x=C([rng.randrange(p) for _ in range(96)])
  z=x**3-x
  if z.is_square():return x,z.sqrt()
M=p**48-1
assert M%96==0
E32=[]
def listall(N,U,V):
 return [add(mu(a,U),mu(b,V)) for a in range(N) for b in range(N)]
for j in range(2):
 while True:
  P=mu(M//32,point())
  if mu(16,P) is None:continue
  if E32 and mu(16,E32[0])==mu(16,P):continue
  E32.append(P);break
E3=[]
for j in range(2):
 while True:
  P=mu(M//3,point())
  if P is None:continue
  if E3 and P in (E3[0],neg(E3[0])):continue
  E3.append(P);break
U,V=E32
DIRS=[(1,b) for b in range(16)]+[(2*a,1) for a in range(8)]
VDIRS=[(1,b) for b in range(3)]+[(0,1)]
lines=[]
def ii(P):return None if P is None else (-P[0],i*P[1])
def fr(P):return None if P is None else (P[0]**11,P[1]**11)
def bd(P,half):
 return P,ii(P),add(half,fr(half)),ii(add(half,fr(half)))
for u,v in DIRS:
 P=add(mu(u,U),mu(v,V));P16=mu(2,P)
 t=t16(P16,-C(1),C(0))
 for u3,v3 in VDIRS:
  L=add(mu(u3,E3[0]),mu(v3,E3[1]))
  B0,B1,g=velu(-C(1),C(0),[L,neg(L)])
  t1=t16(g(P16),B0,B1)
  if any(f[3]==(t,t1) for f in FS):
   lines.append(((t,t1),bd(P16,P),bd(L,mu(2,L)), (u,v), (u3,v3)))
def pure(r,c,d,B,l,alpha0=0):
 Q=None
 assert (alpha0-c)%2==0 and (r-d)%2==0
 for a,V in zip(((alpha0-c)//2,(r-d)//2,c,d),B):
  Q=add(Q,mu(a%l,V))
 return Q
def eig(r,c,d,B,l,alpha0=0):
 b=pure(r,c,d,B,l,alpha0)
 return next((a for a in range(l) if mu(a,B[0])==b),None)
def triples(m,sp):
 ans=[]
 for r in range(-math.isqrt(m),math.isqrt(m)+1):
  if (m-r*r)%11:continue
  u=(m-r*r)//11
  for c in range(-math.isqrt(u),math.isqrt(u)+1):
   if c%2!=sp or (u-c*c)<0:continue
   d=math.isqrt(u-c*c)
   if d*d!=u-c*c:continue
   for d0 in sorted(set([-d,d])):
    if (r-d0)%2==0:ans.append((r,c,d0))
 return ans
# Exact 241 sign for the identified fixed branch. Over this extension
# pi^96=[11^48], so all 241 torsion is available.
rng=random.Random(311*241)
M=11**48-1
assert M%241==0
def draw():
 while True:
  x=C([rng.randrange(11) for _ in range(96)])
  y=x**3-x
  if not y.is_square():continue
  T=mu(M//241,(x,y.sqrt()),-C(1))
  if T is not None:
   assert mu(241,T,-C(1)) is None
   return T
def app(t,P,d=1):
 r,c,k=t
 return mu(pow(d,-1,241),add(add(mu(r,ii(P),-C(1)),mu(c,fr(P),-C(1)),-C(1)),mu(k,ii(fr(P)),-C(1)),-C(1)),-C(1))
def lm(P,Q,T):
 # Miller line/vertical ratio, using short model -1,0.
 if P is None or Q is None:return T[0]**0
 x,y=P;u,v=Q
 if x==u and y==-v:return T[0]-x
 l=(3*x*x-1)/(2*y) if P==Q else (v-y)/(u-x)
 R=add(P,Q,-C(1))
 assert R is not None and T[0]!=R[0]
 return (T[1]-y-l*(T[0]-x))/(T[0]-R[0])
def mill(k,P,T):
 z=C(1);Q=P
 for b in bin(k)[3:]:
  z=z*z*lm(Q,Q,T);Q=add(Q,Q,-C(1))
  if b=='1':z*=lm(Q,P,T);Q=add(Q,P,-C(1))
 assert Q is None
 return z
def gauss(z):
 assert z!=C(1) and z**241==C(1)
 r=C(1);v=C(0)
 for j in range(1,241):
  r*=z
  v+=r if pow(j,120,241)==1 else -r
 assert v*v==C(241)
 return v
assert C.degree()==96 and C(241)==i*i
# Use the marked pair determined above, not just the underlying j.
record=next(x for x in lines if x[0]==next(f[3] for f in FS if f[0]==[600,593]) and eig(-5,-1,-5,x[1],16,1)==2 and eig(-5,-1,-5,x[2],3,1)==0 and eig(10,-2,-4,x[1],16)==0)

R16=record[1][0];R3=record[2][0]
Orig=ff[296,149];X0,Y0,J0,J20=[at(x,Orig['dimensions']) for x in Orig['exact']]
assert chart(X0,Y0) is not None
def pin(A,L,B):
 S=[]
 for x in base:
  for y in base:
   if y*y==x**8+14*x**4+1 and chart(x,y)==A:S.append((x,y))
 assert S==[(L,B)]
pin(chart(X0,Y0),X0,Y0)
F0=next(f for f in FS if f[0]==[600,593])
pin(F0[3],F0[1],F0[2])
assert [F0[4],Orig['poly_source'],Orig['poly_target'],ff[600,593]['poly_target']]==[4,4,12,12]
assert F0[5]==1
# Actual moving order and the unique admissible auxiliary element:
R16B,R3B=record[1],record[2]
def norm(t):r,c,d=t;return r*r+11*(c*c+d*d)
bad=[]
for t in triples(320,0):
 r,c,d=t
 if r%11!=10:continue
 if eig(*t,R16B,16) not in (0,8):continue
 if eig(*(3*q for q in t),R3B,3) is None:continue
 # 4 sqrt(-5) must be primitive at 2 in the supersingular order.
 isdiv2=all(a%2==0 for a in (-c//2,(r-d)//2,c,d))
 if not isdiv2:bad.append(t)
assert bad==[(10,-2,-4)]
assert norm((-5,-1,-5))==311 and -5%11==6
assert -(311)%241==171 and pow(171,120,241)==240
h0=-288
assert h0 == -3*sum(a*b*w for a,b,w in zip((-5,-1,-5),(10,-2,-4),(1,11,11)))//2
H=5*12*12*311-h0*h0
assert H==140976 and H%11==0 and H%121
print('Q [296,149] chart',list(map(e2,chart(X0,Y0))),'Qprime [600,593] chart',list(map(e2,F0[3])))
print('maximal moving array (-5,-1,-5), ordered alpha (2,0); auxiliary array (10,-2,-4)/2')
print('h0',h0,'norm defect',H,'local length 1; named sqrt(-241*311) = 5 mod 11')

b=next(x for x in range(241) if (x*x+80)%241==0)
U=(10,-2,-4);V=(-5,-1,-5)
for e in (b,-b):
 while True:
  W=draw();P=add(app(U,W,2),mu(e,W,-C(1)),-C(1))
  if P is not None:break
 assert app(U,P,2)==mu(e,P,-C(1))
 Q=app(V,P)
 z=-mill(241,P,Q)/mill(241,Q,P)
 h=gauss(z)
 assert h==-i
 # Literal reverse horizontal quotient of the 241 eigenline.
 K=[];B=P
 for _ in range(240):
   assert B is not None
   K.append(B);B=add(B,P,-C(1))
 assert B is None
 La,Lb,G=velu(-C(1),C(0),K)
 j=1728*4*La**3/(4*La**3+27*Lb**2)
 assert j==J0
 T16=G(R16);T3=G(R3)
 L3,B3,G3=velu(La,Lb,[T3,neg(T3)])
 ck=[t16(T16,La,Lb),t16(G3(T16),L3,B3)]
 print('241 eigenvalue',e%241,'Weil-Gauss sign',-1,'marked Velu quotient',list(map(e2,ck)), 'j',e2(j),flush=True)
 assert tuple(ck)==chart(X0,Y0)

print('two distinct ordered length-one paths, diagonal multiplicity +2 each: subtotal -4 only')