from pathlib import Path
from fractions import Fraction
from itertools import product
import sys,flint,contextlib,io,runpy,json,random,os
from hashlib import sha256
HERE=Path(__file__).resolve().parent
H=HERE.parent
for k,h in [('original-inert29-exact-calibration-field-r1','1f216d1caf9ac4b985132a984aaf191eb51467fa045d6012e3790e7bad0c24a7'),
            ('original-inert29-CM-real-ideal-r2','c763e955648ab6ecc2873fdf2250e69478270cc6cf07a7b63d0c87f5aa528517')]:
 d=H/k
 assert sha256((d/'SHA256SUMS').read_bytes()).hexdigest()==h
 for row in (d/'SHA256SUMS').read_text().splitlines():
  t,f=row.split(maxsplit=1)
  assert sha256((d/f).read_bytes()).hexdigest()==t
with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()):
 E=runpy.run_path(str(HERE/'check_D311_p19_cycle.py'))
L=json.loads((HERE/'EXACT-D311-P19-CANONICAL-2-CYCLE.json').read_text())
assert json.loads(json.dumps(E['data']))==L
p=19;K=8
Cd=flint.fq_default_ctx(p,96)
Z={'poly':[int(a) for a in Cd.modulus().coeffs()],'s':Cd(2).sqrt()}
s0=Z['s'];i=3*s0
assert i*i==-Cd(1) and (5*s0)**2==-Cd(311) and (4*s0)**2==Cd(241)
Ad=-Cd(1)
rng=random.Random(31119)
def a0(P,Q):
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u:
  if y+v==0:return None
  assert y==v
  m=(3*x*x-1)/(2*y)
 else:m=(v-y)/(u-x)
 z=m*m-x-u
 return z,m*(x-z)-y
def neg(P):return None if P is None else (P[0],-P[1])
def m0(k,P):
 if k<0:return m0(-k,neg(P))
 Q=None
 while k:
  if k&1:Q=a0(Q,P)
  k//=2
  if k:P=a0(P,P)
 return Q
def f0(a):
 v=list(a.to_list())+[0,0]
 return Cd(int(v[0]))+int(v[1])*s0
def cp(P):
 return [f0(a) for a in P.coeffs()]
rho=E['Al'][0];Data=[cp(t) for t in (rho.x,rho.y,rho.x.derivative(),rho.y.derivative())]
def pev(coeff,v):
 u=Cd(0)
 for x in reversed(coeff): u=u*v+x
 return u
def alpha(P):
 if P is None:return None
 x,y=P;A,B,a,b=(pev(z,x) for z in Data)
 if B==0:return None
 C=A/B
 return C,y*(a-C*b)/(B*((1+5*s0)/2))
def direct_V(P):
 if P is None:return None
 x,y=P
 Q=(x**p,y**p)
 return a0(a0(m0(8,(-x,i*y)),m0(3,Q)),m0(2,(-Q[0],i*Q[1])))
def point(l):
 for _ in range(45):
  x=Cd([rng.randrange(p) for _ in range(96)])
  g=x**3-x
  if not g.is_square():continue
  P=m0((p**48-1)//l,(x,g.sqrt()))
  if P is None:continue
  if l==16 and m0(8,P) is None:continue
  return P
 raise AssertionError('fixed small torsion attempt')
def mark(n,j,l):
 for _ in range(30):
  P=point(n)
  Q=a0(alpha(P),m0(-l,P))
  if Q is None or (n==16 and m0(8,Q) is None):continue
  assert m0(n,Q) is None and alpha(Q)==m0(j,Q)
  return Q
 raise AssertionError('missing literal mark')
T16=mark(16,2,15);T3=mark(3,0,1)
P0=point(241);V0=direct_V(P0)
assert V0==a0(m0(2,alpha(P0)),neg(P0))
def mm(P,Q,T):
 if P is None or Q is None:return Cd(1)
 x,y=P;u,v=Q
 if x==u and y==-v:return T[0]-x
 d=(3*x*x-1)/(2*y) if P==Q else (v-y)/(u-x)
 R=a0(P,Q)
 assert R is not None
 return (T[1]-y-d*(T[0]-x))/(T[0]-R[0])
def mll(P,T):
 a=Cd(1);Q=P
 for b in bin(241)[3:]:
  a=a*a*mm(Q,Q,T);Q=a0(Q,Q)
  if b=='1':a*=mm(Q,P,T);Q=a0(Q,P)
 assert Q is None
 return a
g0=-mll(P0,V0)/mll(V0,P0)
assert g0!=1 and g0**241==1
G0=sum((1 if pow(x,120,241)==1 else -1)*g0**x for x in range(1,241))
assert G0 in (4*s0,-4*s0)
sgn=1 if G0==4*s0 else -1
print('all actual moving tame marks present; Weil sign',sgn,file=sys.stderr)
M=p**K
CQ=flint.fmpz_mod_poly_ctx(M)
G=CQ(Z['poly'])
class R:
 def __init__(self,v):
  if isinstance(v,R):self.v=v.v
  elif isinstance(v,type(G)):self.v=v
  elif isinstance(v,(int,Fraction)):
   a=Fraction(v);self.v=CQ(a.numerator*pow(a.denominator,-1,M)%M)
  else:self.v=CQ(list(map(int,v)))
 def __add__(self,v):return R(self.v+R(v).v)
 __radd__=__add__
 def __neg__(self):return R(-self.v)
 def __sub__(self,v):return self+-R(v)
 def __rsub__(self,v):return R(v)-self
 def __mul__(self,v):return R((self.v*R(v).v)%G)
 __rmul__=__mul__
 def __truediv__(self,v):return self*R(v).inv()
 def __rtruediv__(self,v):return R(v)*self.inv()
 def __eq__(self,v):return self.v==R(v).v
 def __pow__(self,n):return R(self.v.pow_mod(n,G))
 def val(self):
  def a(v):
   if not v:return K
   k=0
   while v%p==0:v//=p;k+=1
   return k
  return min((a(int(u)) for u in self.v.coeffs()),default=K)
 def mod(self):return Cd([int(x)%p for x in self.v.coeffs()])
 def inv(self):
  u=self.mod()
  assert u,('nonunit',self.val())
  A=R((1/u).to_list())
  for k in range((K-1).bit_length()):A=A*(2-A*self)
  assert A*self==1
  return A
def ra(v):return R(v.to_list())
def sol(x,f):
 for i in range(K.bit_length()+1):
  a,b=f(x)
  if a==0:return x
  x-=a/b
 assert f(x)[0]==0
 return x
s=sol(ra(Z['s']),lambda x:(x*x-2,2*x))
A0=sol(R(8),lambda a:(a**4+4*a*a-1,4*a**3+8*a))
i0=sol(3*s,lambda a:(a*a+1,2*a))
z3=sol(12*s,lambda a:(a*a-3,2*a))
def enc(t):a,b=t;return a+b*s
def dec(t):
 h=next(i for i,u in enumerate(s.v.coeffs()) if i and int(u)%p)
 c=int(t.v[h])*pow(int(s.v[h]),-1,M)%M
 d=(int(t.v[0])-c*int(s.v[0]))%M
 assert enc((d,c))==t
 return [d,c]
Bt=enc(L['source_model'][1]);At=R(-1)
def curve(x):return x**3+At*x+Bt
def ad(P,Q,A=At):
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
def mult(k,P,A=At):
 Q=None
 while k:
  if k&1:Q=ad(Q,P,A)
  k//=2
  if k:P=ad(P,P,A)
 return Q
def tor_lift(P0,l):
 x0,y0=P0
 def pt(x):return x,sol(ra(y0),lambda y:(y*y-curve(x),2*y))
 def crit(x):
  P=pt(x)
  if l==16:
   X,Y=mult(8,P)
   return Y,8*(3*X*X+At)/(2*P[1])
  k=l//2
  Q,T=mult(k,P),mult(k+1,P)
  return T[0]-Q[0],((k+1)*T[1]-k*Q[1])/P[1]
 x=sol(ra(x0),crit)
 P=pt(x)
 assert (mult(8,P)[1]==0 if l==16 else mult(l//2,P)[0]==mult(l//2+1,P)[0])
 assert (P[0].mod(),P[1].mod())==P0
 return P
def vel(A,B,K):
 # K is one representative X-coordinate from each ± pair for odd
 # order, or the sole rational 2-kernel point if even.
 sgn=1 if len(K)==1 and (K[0]**3+A*K[0]+B)==0 else 2
 ss=[x**3+A*x+B for x in K]
 a=A-5*sgn*sum(3*x*x+A for x in K)
 b=B-7*sgn*sum(5*x**3+3*A*x+2*B for x in K)
 def g(T):
  x,y=T
  xf=x**3+A*x+B;f1=3*x*x+A
  U=x;J=R(1)
  for k,kf in zip(K,ss):
   v=(x-k).inv()
   w=xf+kf
   if sgn==1:
    U+=w*v**2-x-2*k
    J+=f1*v**2-2*w*v**3-1
   else:
    U+=2*(w*v**2-x-2*k)
    J+=2*(f1*v**2-2*w*v**3-1)
  V=y*J
  assert V*V==U**3+a*U+b
  return U,V
 return a,b,g
def t8(P,A):
 r=mult(4,P,A)[0];b=3*r*r+A
 u=mult(2,P,A)[0]-r;v=P[0]-r
 assert u*u==b
 return 32/((v+b/v)/u-6)
def t16(P,A,B):
 a0=t8(mult(2,P,A),A)
 A1,B1,F=vel(A,B,[mult(8,P,A)[0]])
 a1=t8(F(P),A1)
 t=(a1-2*a0)/(a0+4)
 assert t*t/(t+2)==a0 and t*(t+4)==a1
 return t
def at(X,n,aa,z3):
 Id=[(0,0),(0,2)]+[(k,j) for j in range(n//4) for k in range(4) if (k,j) not in ((0,0),(0,2))]
 return sum(R(Fraction(v))*aa**k*i0**(j&1)*s**(j>>1&1)*z3**(j>>2&1) for v,(k,j) in zip(X,Id))
def basis(T):
 X,Y=T;u=Y+X**4
 return [1,u]+[X**k*(u+7) for k in range(1,5)]
def w48(T):
 X,Y=T;return (X+1)/(X-1),4*Y/(X-1)**4
def w3(T):
 X,Y=T;return -1/X,-Y/X**4
ib=[lambda v:v,lambda v:w48(w3(v)),w3,w48]
def ar(K,x,y):
 v=2+2*(x[5]+y[5])-2*x[1]*y[1]+2*x[3]*y[3]
 return (v-x[2]*y[4]-x[4]*y[2]) if K==5 else (v-x[2]*y[2]-x[4]*y[4])
P=tor_lift(P0,241);R16=tor_lift(T16,16);R3=tor_lift(T3,3)
ker=[P[0]];b=P
for j in range(2,121):
 b=ad(b,P)
 ker.append(b[0])
la,lb,phi=vel(At,Bt,ker)
Q16=phi(R16);Q3=phi(R3)
u=t16(Q16,la,lb)
a3,b3,phi3=vel(la,lb,[Q3[0]])
v=t16(phi3(Q16),a3,b3)
res=[]
for a,b in product(range(p),repeat=2):
 x=Cd(a)+b*s0;t=(v.mod()+2)*x+1
 if x==0 or t==0 or (u.mod()+2-x)*t-3*x!=0:continue
 y=2*t-x**4-1
 if y*y==x**8+14*x**4+1:res.append((x,y))
assert len(res)==1,res
X,Y=map(ra,res[0])
t=u
for n in range(K.bit_length()+1):
 V=Y+X**4+1;U=t+2-X
 f=Y*Y-X**8-14*X**4-1;g=U*V-6*X
 if f==g==0:break
 fx=-8*X**7-56*X**3;fy=2*Y;gx=4*X**3*U-V-6;gy=U
 det=fx*gy-fy*gx
 X,Y=X-(f*gy-fy*g)/det,Y-(fx*g-f*gx)/det
assert Y*Y==X**8+14*X**4+1
b=(Y+X**4+1)/2
assert (X-2+3*X/b,(b-2*X-1)/X)==(u,v)
print('actual ordered movable chart (X,Y)',dec(X),dec(Y),'kernel count',len(ker)*2,file=sys.stderr)
F=json.loads((H/'original-inert29-exact-calibration-field-r1/EXACT-CALIBRATION-FIELD.json').read_text())
FP={tuple(row['flag']):row for row in F['exact_flags']}
Q=json.loads((H/'original-inert29-CM-real-ideal-r2/EXACT-REAL-CM-CUBIC.json').read_text())
S=[basis(f((X,Y))) for f in ib]
allres=[]
for sa,sb in ((1,1),(1,-1),(-1,1),(-1,-1)):
 arr=[];aa=A0 if sa==1 else i0/A0
 for k,Dd,PQ,ex in Q['signed_whole_packets']:
  for xy in PQ:
   d=FP[tuple(xy)]
   w=basis(tuple(at(y,d['dimensions'],aa,sb*z3) for y in d['exact'][:2]))
   rr=[ar(k,w,b).val() for b in S]
   arr.append((k,xy,ex,rr))
 assert len(arr)==40 and max(x for rr in arr for x in rr[3])<K
 tot=sum(e*(r[0]+r[1]-r[2]-r[3]) for k,xy,e,r in arr)
 allres.append(dict(sqrt5=sa*9,sqrt6=sb*5,raw=tot,maxdepth=max(x for rr in arr for x in rr[3]),factors=arr))
e=sgn*sum((1 if z['sqrt5']==9 else -1)*z['raw'] for z in allres)
print('four raw values',[(r['sqrt5'],r['sqrt6'],r['raw'],r['maxdepth']) for r in allres],'named binary contribution',e,'mod13',e%13,file=sys.stderr)
assert sgn==1 and e==0 and [z['raw'] for z in allres]==[0,0,0,0]
assert all(z['maxdepth']==1 for z in allres)
print(json.dumps(dict(D=-311,prime=19,precision=K,genus_sign=sgn,binary_M5_named_root=-1,arc_projection=e,actual_X=dec(X),actual_Y=dec(Y),t16=dec(u),t16_3=dec(v),all_places=allres),indent=2,sort_keys=True),flush=True)
sys.stdout.flush();os._exit(0)
