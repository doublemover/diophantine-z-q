from pathlib import Path
from fractions import Fraction as F
from itertools import product
import sys,json,io,contextlib,runpy,math,flint,random,os
from hashlib import sha256
HERE=Path(__file__).resolve().parent
h=HERE.parent
root=HERE.parents[2]
donors=[
 (h/'original-inert29-exact-calibration-field-r1','1f216d1caf9ac4b985132a984aaf191eb51467fa045d6012e3790e7bad0c24a7'),
 (h/'original-inert29-CM-real-ideal-r2','c763e955648ab6ecc2873fdf2250e69478270cc6cf07a7b63d0c87f5aa528517'),
 (h/'original-D311-inert19-canonical-one-arc-r1','5b5a019f598e2eae7449e2a786b9b1bea3fe6c0a49a87a4703ce47691ccdeb75'),
 (root/'rc-native-helper-20261120/ct-level48-inert-prime19-two-oriented-seeds-r1','bf5c71646c98d5876dd7199ac3bcf671174bce0c4b7f67f883d23194311e1fd7'),
 (root/'rc-native-helper-20261120/ct-level48-D311-p11-class-and-p19-candidate-r1','bf1163c367cb2e9d7630f24ccb86c549c7fecb5e5467fb5fdc312908ff39be5d'),
]
for dd,hh in donors:
 assert sha256((dd/'SHA256SUMS').read_bytes()).hexdigest()==hh
 for row in (dd/'SHA256SUMS').read_text().splitlines():
  hv,f=row.split(maxsplit=1)
  assert sha256((dd/f).read_bytes()).hexdigest()==hv

d0=h/'original-inert29-exact-calibration-field-r1'
with contextlib.redirect_stdout(io.StringIO()):A0=runpy.run_path(str(d0/'check_exact_calibration_field.py'))
D=json.loads((d0/'EXACT-CALIBRATION-FIELD.json').read_text())
S={tuple(r['flag']):r for r in D['exact_flags']}
U0=A0['Arit'](2);c,p,a,m=U0.c,U0.p,U0.add,U0.m
def e(q):return list(map(F,q))
def bb(P):
 X,Y=P;zz=a(Y,p(X,4));g=a(zz,c(7))
 return [c(1),zz]+[m(p(X,j),g) for j in range(1,5)]
P=tuple(map(e,S[81,614]['exact'][:2]))
Qx,Qy=map(e,S[184,314]['exact'][:2]);Q=(Qx,U0.u(-1,Qy))
X,Y=bb(P),bb(Q)
R=a(c(2),U0.u(2,a(X[5],Y[5])),U0.u(-2,m(X[1],Y[1])),U0.u(-1,m(X[2],Y[2])),U0.u(2,m(X[3],Y[3])),U0.u(-1,m(X[4],Y[4])))
assert not any(R)
# Exact source and target class polynomial checks for the deck-flipped flag.
Dpol=json.loads((root/'rc-native-helper-20261120/ct-level48-Kminus5-exact-calibration-lifts-r1/EXACT-KMINUS5-CALIBRATION-LIFTS.json').read_text())['exact_order_class_polynomials']['4']
def homogeneous_j(Xn,Xd,Yn,Yd):
 u=U0.u
 assert Yd==p(Xd,4)
 B=a(Yn,p(Xn,4),Yd)
 N=a(m(a(Xn,u(-2,Xd)),B),u(6,m(Xn,Yd)))
 B=m(Xd,B)
 for d in (2,4,16):N,B=p(N,2),m(B,a(N,u(d,B)))
 return p(a(N,u(256,B)),3),m(B,p(N,2))
for args in ((Q[0],c(1),Q[1],c(1)),(a(Q[0],c(1)),a(Q[0],c(-1)),U0.u(4,Q[1]),p(a(Q[0],c(-1)),4))):
 N,Dn=homogeneous_j(*args)
 assert any(Dn)
 R=c(0);B=c(1)
 for k in Dpol:
  R=a(m(R,N),U0.u(k,B))
  B=m(B,Dn)
 assert not any(R)
Vcal=json.loads((h/'original-inert29-CM-real-ideal-r2/EXACT-REAL-CM-CUBIC.json').read_text())
assert any(k==7 and DD==-320 and [81,614] in A and e==1 for k,DD,A,e in Vcal['signed_whole_packets'])
print('exact char0 H7 incidence P=(81,614), deck-fixed Q=(184,556)',file=sys.stderr)
# finite j7 trace and line selection, purely bounded to this one label.
pp=19;C=flint.fq_default_ctx(pp,96);s=C(2).sqrt();i=3*s;A1=C(-1);B1=C(5)
assert i*i==-C(1)
def fqa(x):return sum(C(F(v).numerator)/C(F(v).denominator)*C(8)**k*i**(j&1)*s**(j>>1&1)*(12*s)**(j>>2&1) for v,(k,j) in zip(x,U0.I))
X,Y=map(fqa,Q);assert Y*Y==X**8+14*X**4+1
F0=[C(a)+b*s for a,b in product(range(pp),repeat=2)]
def enc(u):return next(a+pp*b for a,b in product(range(pp),repeat=2) if C(a)+b*s==u)
assert (enc(X),enc(Y))==(100,39)
r0=(Y+X**4+1)/2
t0=X-2+3*X/r0;t1=(r0-2*X-1)/X
tt=t0
for a in (2,4,16):tt=tt*tt/(tt+a)
assert (tt+256)**3/(tt*tt)==7
def ng(P):return None if P is None else (P[0],-P[1])
def add(P,Q,A=A1):
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u:
  if y+v==0:return None
  assert y==v
  m=(3*x*x+A)/(2*y)
 else:m=(v-y)/(u-x)
 z=m*m-x-u
 return z,m*(x-z)-y
def mul(n,P,A=A1):
 if n<0:return mul(-n,ng(P),A)
 Q=None
 while n:
  if n&1:Q=add(Q,P,A)
  n//=2
  if n:P=add(P,P,A)
 return Q
def ve(A,B,L):
 AA=A-5*sum(3*x*x+A for x,y in L)
 BB=B-7*sum(5*x**3+3*A*x+2*B for x,y in L)
 def g(P):
  if P in L or P is None:return None
  x,y=P
  for J in L:
   u,v=add(P,J,A)
   x+=u-J[0];y+=v-J[1]
  assert y*y==x**3+AA*x+BB
  return x,y
 return AA,BB,g
def t8(P,A):
 r=mul(4,P,A)[0];b=3*r*r+A
 u=mul(2,P,A)[0]-r;v=P[0]-r
 assert u*u==b
 return 32/((v+b/v)/u-6)
def t16(P,A,B):
 a0=t8(mul(2,P,A),A)
 a,b,g=ve(A,B,[mul(8,P,A)])
 a1=t8(g(P),a)
 t=(a1-2*a0)/(a0+4)
 assert t*t/(t+2)==a0 and t*(t+4)==a1
 return t
rn=random.Random(19311)
def draw(l):
 for _ in range(30):
  x=C([rn.randrange(pp) for _ in range(96)]);f=x**3-x+5
  if not f.is_square():continue
  R=mul((pp**48-1)//l,(x,f.sqrt()))
  if R is not None:return R
 raise ValueError('torsion')
def basis(l,powr):
 n=l**powr;V=[]
 for _ in range(32):
  P=draw(n);T=mul(n//l,P)
  if T is None:continue
  if V and T in [mul(a,mul(n//l,V[0])) for a in range(l)]:continue
  V.append(P)
  if len(V)==2:return V
 raise ValueError('basis')
U,V=basis(2,4);J,K=basis(3,1)
D16=[(1,k) for k in range(16)]+[(2*k,1) for k in range(8)]
D3=[(1,k) for k in range(3)]+[(0,1)]
pairs=[]
for a,b in D16:
 G=add(mul(a,U),mul(b,V));t=t16(G,A1,B1)
 if t!=t0:continue
 for c,d in D3:
  H=add(mul(c,J),mul(d,K))
  a3,b3,V3=ve(A1,B1,[H,ng(H)])
  if t16(V3(G),a3,b3)==t1:pairs.append(((a,b),(c,d),G,H))
assert len(pairs)==1
a,b,G,H=pairs[0];print('Q=(100,39) actual 16/3 direction',a,b,file=sys.stderr)
# Known p19 geometric maximal order nu,eta,pi,eta*pi.
Keta=11+3*s;S0=5+13*s;be=3*Keta*Keta-1
assert 2/S0-1==5*s
def eta(P):
 if P is None or P==(Keta,C(0)):return None
 x,y=P;d=x-Keta
 R=(S0*S0*(x+be/d),S0**3*y*(1-be/(d*d)))
 assert R[1]**2==R[0]**3-R[0]+5
 return R
def fr(P):return None if P is None else tuple(t**19 for t in P)
def end(V,P,l):
 # V coefficients in (nu,eta,pi,eta*pi). nu numerator applied to inv(7)*P.
 a,b,c,d=V
 q=a*pow(7,-1,l)%l
 R=None
 for z,W in ((q,P),(5*q+b,eta(P)),(5*q+c,fr(P)),(4*q+d,eta(fr(P)))):
  R=add(R,mul(z%l,W))
 return R
def coeff(r,c,d):
 # Input pure coords (r,c,d)/14 on (tau,pi,tau*pi).
 if r%2:return None
 a=-r//2;b=-a
 if (d-4*a)%7:return None
 w=(d-4*a)//7
 if (c-14*a-7*w)%14:return None
 z=(c-14*a-7*w)//14
 return a,b,z,w
def eig(V,P,l):return next((t for t in range(l) if end(V,P,l)==mul(t,P)),None)
fixed=[]
for d in range(-11,12):
 for c in range(-29,30):
  rem=80*196-19*c*c-133*d*d
  if rem<0 or rem%7:continue
  r=math.isqrt(rem//7)
  if r*r!=rem//7:continue
  for r0 in sorted({r,-r}):
   if r0%19!=6:continue
   v=coeff(r0,c,d)
   if v is None or all(a%2==0 for a in v):continue
   if eig(v,G,16) not in (0,8) or eig(v,H,3) is None:continue
   fixed.append(((r0,c,d),v,eig(v,G,16),eig(v,H,3)))
print('auxiliary exact f4 calibrated candidates:',fixed,file=sys.stderr)
assert len(fixed)==1
# The absolute trace convention x = Trd(W * beta), beta=4sqrt(-5).
# For W/241 returning the moving alpha at 16,3.
u=fixed[0][0];n=311*241**2*196
x=112
G0=[7*u[0],19*u[1],133*u[2]]
# Choose free axis for D, eliminate C exactly via its coefficient.
U0,U1,U2=G0
assert U1!=0
W0=[]
for d in range(-math.isqrt(n//133),math.isqrt(n//133)+1):
 v=-98*x-U2*d
 K2=7*U1*U1+19*U0*U0
 K1=-38*U0*v
 K0=19*v*v-(n-133*d*d)*U1*U1
 delta=K1*K1-4*K2*K0
 if delta<0:continue
 z=math.isqrt(delta)
 if z*z!=delta:continue
 for z0 in sorted({z,-z}):
  if (z0-K1)%(2*K2):continue
  r=(z0-K1)//(2*K2)
  if (v-U0*r)%U1:continue
  c=(v-U0*r)//U1
  if r%19!=11:continue
  w=coeff(r,c,d)
  if w is None:continue
  aa=[k+241*j for k,j in zip(w,(7,-5,-5,-4))]
  if any(k%2 for k in aa):continue
  aa=[k//2 for k in aa]
  assert 7*r*r+19*c*c+133*d*d==n and sum(k*v for k,v in zip(G0,(r,c,d)))==-98*x
  e16=eig(aa,G,16);e3=eig(aa,H,3)
  W0.append(((r,c,d),w,e16,e3))
print('single x112 genuinely integral and named-filtered candidates:',W0,file=sys.stderr)
sel=[r for r in W0 if r[2:]==(2*(241%16)%16,0)]
print('full 16/3 marked x112:',sel,file=sys.stderr)
assert len(sel)==1
r,w,e16,e3=sel[0]
assert any(x%241 for x in w)
Ew=[(z+241*j)//2 for z,j in zip(w,(7,-5,-5,-4))]
for _ in range(20):
 K0=draw(241);Wx=end(w,K0,241)
 if Wx is not None:break
else:raise AssertionError('nonzero nilpotent missing')
assert end(w,Wx,241) is None
def ml(P,Q,A):
 def line(P1,P2,T):
  if P1 is None or P2 is None:return C(1)
  x,y=P1;u,v=P2
  if x==u and y==-v:return T[0]-x
  t=(3*x*x+A)/(2*y) if P1==P2 else (v-y)/(u-x)
  P3=add(P1,P2,A)
  assert P3 is not None
  return (T[1]-y-t*(T[0]-x))/(T[0]-P3[0])
 R=P;g=C(1)
 for b in bin(241)[3:]:
  g=g*g*line(R,R,Q);R=add(R,R,A)
  if b=='1':g*=line(R,P,Q);R=add(R,P,A)
 assert R is None
 return g
def chia(P,Q,A):
 e=-ml(P,Q,A)/ml(Q,P,A)
 assert e!=1 and e**241==1
 G0=sum((1 if pow(x,120,241)==1 else -1)*e**x for x in range(1,241))
 assert G0 in (4*s,-4*s)
 return 1 if G0==4*s else -1
ch=chia(K0,Wx,A1)
print('exact source determinant Weil sign',ch,file=sys.stderr)
L7=[mul(t,Wx) for t in range(1,241)]
assert len(set(L7))==240
A19,B19,g2=ve(A1,B1,L7)
R16,R3,Sf=map(g2,(G,H,K0))
assert Sf is not None and mul(241,Sf,A19) is None
tmax16=t16(R16,A19,B19)
a03,b03,g3=ve(A19,B19,[R3,ng(R3)])
tmax3=t16(g3(R16),a03,b03)
print('physical moving maximal quotient j',enc((1728*4*A19**3)/(4*A19**3+27*B19**2)),file=sys.stderr)
Fdata=[]
for PP,ell in ((U,16),(V,16),(J,3),(K,3)):
 a1=g2(PP);a2=mul(pow(241,-1,ell),g2(end(Ew,PP,ell)),A19)
 Fdata.append((a1,a2))
# Match the existing moving canonical cycle using equality of alpha on full
# E[16] and E[3], more than the degree bound for an endomorphism difference.
cycle=h/'original-D311-inert19-canonical-one-arc-r1/check_D311_p19_cycle.py'
with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()):
 E=runpy.run_path(str(cycle))
L=E['data'];assert json.loads(json.dumps(L))==json.loads(cycle.with_name('EXACT-D311-P19-CANONICAL-2-CYCLE.json').read_text());JF=E['F'];z0=E['s'];rho=E['Al'][0];tx=E['x'];jR=E['R'];red=E['rem']
def conv(x):
 a=list(x.to_list())+[0,0]
 return C(int(a[0]))+int(a[1])*s
def transdata(rho):
 return [[conv(v) for v in q.coeffs()] for q in (rho.x,rho.y,rho.x.derivative(),rho.y.derivative())]
def pol(v,x):
 y=C(0)
 for a in reversed(v):y=y*x+a
 return y
def alp(data,P):
 if P is None:return None
 x,y=P;A,B,Ad,Bd=(pol(v,x) for v in data)
 if B==0:return None
 a=A/B
 return a,y*(Ad-a*Bd)/(B*((1+5*s)/2))
def scale(d,P):return None if P is None else (d*d*P[0],d**3*P[1])
matched=[]
for j,(k0,a,b,_) in enumerate(L['horizontal_cycle']):
 a0,a1=a;b0,b1=b
 aa=C(a0)+a1*s;bb=C(b0)+b1*s
 for u in F0:
  if u==0 or u**4*A19!=aa or u**6*B19!=bb:continue
  data=transdata(rho)
  if all(alp(data,scale(u,x))==scale(u,y) for x,y in Fdata):matched.append((j,u,data,aa,bb))
 k0=JF(k0[0])+k0[1]*z0
 bj=3*k0*k0+JF(a0%19)+(a1%19)*z0
 rj=rho.sub(tx+k0)-k0;zj=rj+bj/rj
 a0,a1=red(zj.x,bj);b0,b1=red(zj.y,bj)
 assert a0*b1==a1*b0
 rho=(jR(a0,b0) if b0 else jR(a1,b1)).sub(tx-k0)+k0
assert len(matched)==2 and matched[0][0]==matched[1][0]
assert matched[0][1]==-matched[1][1]
vtx,d,data,aa,bb=matched[0];G3=scale(d,R3);G16=scale(d,R16);Ff=scale(d,Sf)
assert alp(data,G3) is None and alp(data,G16)==mul(2,G16,aa)
Vd=add(mul(2,alp(data,Ff),aa),ng(Ff),aa)
assert chia(Ff,Vd,aa)==ch
def encx(x):return [int(a) for a in x.to_list()]
def eQ(P):return [encx(t) for t in P]
out=dict(D=-311,prime=19,f=241,trace=112,genus_sign=ch,vertex=vtx,named_target_Q29=[184,556],named_target_Q19=[100,39],
 shell_aux_coeff=list(fixed[0][1]),shell_W_coeff=list(w),arena_poly=[int(t) for t in C.modulus().coeffs()],s=encx(s),
 R16=eQ(G16),R3=eQ(G3),R241=eQ(Ff),scale=enc(d))
assert vtx==18 and ch==-1
print(json.dumps(out,indent=2,sort_keys=True),flush=True)
print('matched single oriented shell to moving canonical vertex',vtx,'scale',enc(d),'dual Weil sign',ch,file=sys.stderr)
sys.stdout.flush();os._exit(0)
