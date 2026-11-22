from pathlib import Path
from fractions import Fraction
from hashlib import sha256
import sys,flint,contextlib,io,runpy,json,time
H=Path(__file__).resolve().parent.parent
sdir=H/'original-D311-inert11-local-subtotal-r1'
cdir=H/'original-D311-inert11-canonical-cycle-r1'
for d,h in [(sdir,'c6242b9e11b968fc547075df802e9d241f1c24e18ba2d4d577e8bd6bd41ddf22'),(cdir,'e82fc6e663cb456f48ade6f4085123d2757e96ec0ff7ad6b93a22dc35a932fa2')]:
 assert sha256((d/'SHA256SUMS').read_bytes()).hexdigest()==h
 for row in (d/'SHA256SUMS').read_text().splitlines():
  h0,f=row.split(maxsplit=1)
  assert sha256((d/f).read_bytes()).hexdigest()==h0
with contextlib.redirect_stdout(io.StringIO()):Z=runpy.run_path(str(sdir/'check_D311_p11_subtotal.py'))
L=json.loads((cdir/'EXACT-D311-P11-CANONICAL-2-CYCLE.json').read_text())
Cd=Z['C'];K=5
M=11**K
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
   while v%11==0:v//=11;k+=1
   return k
  return min((a(int(u)) for u in self.v.coeffs()),default=K)
 def mod(self):return Cd([int(x)%11 for x in self.v.coeffs()])
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
A0=sol(s,lambda a:(a**4+4*a*a-1,4*a**3+8*a))
i0=sol(4*s,lambda a:(a*a+1,2*a))
z3=sol(R(5),lambda a:(a*a-3,2*a))
def enc(t):a,b=t;return a+b*s
def dec(t):
 c=int(t.v[4])*pow(int(s.v[4]),-1,M)%M
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
def at(X,n):
 Id=[(0,0),(0,2)]+[(k,j) for j in range(n//4) for k in range(4) if (k,j) not in ((0,0),(0,2))]
 return sum(R(Fraction(v))*A0**k*i0**(j&1)*s**(j>>1&1)*z3**(j>>2&1) for v,(k,j) in zip(X,Id))
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
FF=Z['ff'];X0,Y0=(at(w,FF[296,149]['dimensions']) for w in FF[296,149]['exact'][:2])

P0=Z['P'];Q0=Z['Q'];assert Z['e']%241==142
Rc=Z['add'](Z['app'](Z['U'],Q0,2),Z['mu'](99,Q0,-Cd(1)),-Cd(1))
assert Rc is not None and Z['app'](Z['U'],Rc,2)==Z['mu'](99,Rc,-Cd(1))
assert Z['gauss'](-Z['mill'](241,Rc,Z['app'](Z['V'],Rc))/Z['mill'](241,Z['app'](Z['V'],Rc),Rc))==-Z['i']
R16=tor_lift(Z['R16'],16);R3=tor_lift(Z['R3'],3)
P=json.loads((H/'original-inert29-CM-real-ideal-r2/EXACT-REAL-CM-CUBIC.json').read_text())
WG=[]
for j,DD,Arr,eps in P['signed_whole_packets']:
 for ix in Arr:
  d=FF[tuple(ix)]
  w=basis(tuple(at(x,d['dimensions']) for x in d['exact'][:2]))
  WG.append((j,ix,eps,w))
assert len(WG)==40

def arc(e,P0):
 # Kernel e=142, the final one carried by the exact two-path donor.
 P=tor_lift(P0,241)
 print('lifted ordered 241 generator for eigenvalue',e,file=sys.stderr)
 ker=[P[0]];bb=P
 for m in range(2,121):
  bb=ad(bb,P)
  ker.append(bb[0])
 la,lb,phi=vel(At,Bt,ker)
 Q16=phi(R16);Q3=phi(R3)
 u=t16(Q16,la,lb)
 la3,lb3,phi3=vel(la,lb,[Q3[0]])
 v=t16(phi3(Q16),la3,lb3)
 print('exact marked quotient parameters mod 11^K',dec(u),dec(v),file=sys.stderr)
 def par(x):
  b=(v+2)*x+1
  return (u+2-x)*b-3*x,(u+2-x)*(v+2)-b-3
 X=sol(R([int(y)%11 for y in X0.v.coeffs()]),par)
 Y=2*((v+2)*X+1)-X**4-1
 assert Y*Y==X**8+14*X**4+1
 def chart(x,y):
  B=(y+x**4+1)/2
  return x-2+3*x/B,(B-2*x-1)/x
 assert chart(X,Y)==(u,v)
 print('lifted marked (X,Y)',dec(X),dec(Y),'distance from calibrated Q',min((X-X0).val(),(Y-Y0).val()),file=sys.stderr)
 assert min((X-X0).val(),(Y-Y0).val())==1

 T=[basis(f((X,Y))) for f in ib]
 res=[]
 for j,ix,eps,w in WG:
  S=[ar(j,w,y).val() for y in T]
  res.append([j,ix,eps,S])
  if ix==[296,149] and j==5:assert S==[2,0,0,0]
 print('resolved',sum(v<K for _,_,_,l in res for v in l),'of',len(res)*4,'max',max(v for _,_,_,l in res for v in l),file=sys.stderr)
 if all(v<K for _,_,_,ll in res for v in ll):
  tot=sum(e*(t[0]+t[1]-t[2]-t[3]) for j,ix,e,t in res)
  print('ALL FACTORS resolved; exact v11(U)',tot,'moving sign −1; arc contribution',-tot,file=sys.stderr)
  return dict(aux_eigenvalue=e,X=dec(X),Y=dec(Y),t16=dec(u),t16_3=dec(v),factors=res,raw_U_valuation=tot,genus_sign=-1,oriented_contribution=-tot)
 raise AssertionError('precision too low')
out=[arc(99,Rc),arc(142,P0)]
assert [x['oriented_contribution'] for x in out]==[0,0]
assert all(len(x['factors'])==40 and max(v for r in x['factors'] for v in r[3])==2 for x in out)
assert out[0]['factors']==out[1]['factors']
assert [(r['X'],r['Y']) for r in out]==[([39311,2771],[112926,125334]),([105619,112639],[40315,21131])]
print(json.dumps({'scope':'full contributions of exactly the two actual 241 arcs, not the entire named prime','prime':11,'D':-311,'precision':5,'arcs':out},indent=2,sort_keys=True))
