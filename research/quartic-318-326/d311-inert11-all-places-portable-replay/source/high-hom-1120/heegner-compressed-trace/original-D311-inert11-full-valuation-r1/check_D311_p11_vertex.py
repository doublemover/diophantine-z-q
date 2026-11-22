from pathlib import Path
from hashlib import sha256
import os,sys,json,flint,runpy,io,contextlib,time,random,math
H=Path(__file__).resolve().parent.parent
d=H/'original-D311-inert11-complete-two-arcs-r1';c=H/'original-D311-inert11-canonical-cycle-r1'
for q,h in [(d,'f4835b8267248c61feb57000bd75a5e376476bf63c98321ea916ac9034ced45c'),
 (c,'e82fc6e663cb456f48ade6f4085123d2757e96ec0ff7ad6b93a22dc35a932fa2')]:
 assert sha256((q/'SHA256SUMS').read_bytes()).hexdigest()==h
 for row in (q/'SHA256SUMS').read_text().splitlines():
  hv,f=row.split(maxsplit=1)
  assert sha256((q/f).read_bytes()).hexdigest()==hv
with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()):
 E0=runpy.run_path(str(d/'check_D311_p11_complete_arcs.py'))
 E1=runpy.run_path(str(c/'check_D311_p11_canonical_cycle.py'))
# Shared exact mod-11^5 ring and class-calibrated endpoints.
R=E0['R'];s=E0['s'];K=E0['K'];M=E0['M'];Cd=E0['Cd'];Z=E0['Z'];L=E0['L']
B=E0['s'].mod(); enc,dec,sol,ra=[E0[n] for n in ('enc','dec','sol','ra')]
sP=E0['Rc'];sQ=E0['P0']; s3=Z['R3'];rn=random.Random(1112985)
OA=-Cd(1)
f_ad=Z['add'];f_mu=Z['mu'];f_ve=Z['velu'];ng=Z['neg']; app=Z['app']
r_ad=E0['ad'];r_mu=E0['mult']
# Decompose V in the actual torsion basis. Degree-two transport preserves
# its matrix and genus signs because (2/241)=+1.
one=Cd(1)
ta=[None,sP];tb=[None,sQ]
for j in range(2,241):
 ta.append(f_ad(ta[-1],sP,OA));tb.append(f_ad(tb[-1],sQ,OA))
def cod(A):return None if A is None else tuple(tuple(int(v) for v in u.to_list()) for u in A)
la={cod(T):i for i,T in enumerate(ta)}
def find(T):
 for j,b in enumerate(tb):
  x=f_ad(T,ng(b),OA)
  if cod(x) in la:return (la[cod(x)],j)
 raise AssertionError('not in the 241 basis')
va,vb=[find(app(Z['V'],t)) for t in (sP,sQ)]
assert (va[0]+vb[1])%241==0 and (va[0]*vb[1]-va[1]*vb[0])%241==311%241
def wpair(A,B):return -Z['mill'](241,A,B)/Z['mill'](241,B,A)
gg=Z['gauss'](wpair(sP,sQ))
assert gg in (Z['i'],-Z['i'])
wg=1 if gg==Z['i'] else -1
def phase(a,b):
 c,d=(a*va[k]+b*vb[k] for k in range(2))
 g=(a*d-b*c)%241
 assert g
 return wg*(1 if pow(g,120,241)==1 else -1)
assert phase(1,0)==phase(0,1)==-1
DIR=[(1,x) for x in range(241)]+[(0,1)]
assert sum(phase(*v) for v in DIR)==0
assert (va,vb,wg)==((167,129),(28,74),1)
def f121(k):
 a=list(k.to_list())+[0,0]
 return Cd(int(a[0]))+int(a[1])*B
def poly_data(Q):
 return [f121(T) for T in Q.coeffs()]
def crop(T):
 # Avoid importing another extension context into the ambient one.
 V=[]
 for Q in (T.x,T.y,T.x.derivative(),T.y.derivative()):V.append(poly_data(Q))
 return V
def px(H,z):
 v=Cd(0)
 for k in reversed(H):v=v*z+k
 return v
def applyalpha(Dd,T):
 x,y=T
 ux,uy,dx,dy=[px(D,x) for D in Dd]
 if uy==0:return None
 return ux/uy,y*(dx*uy-ux*dy)/(uy*uy*((1+2*B)/2))
def choose16(A,B0,Dd):
 for rep in range(40):
  for _ in range(20):
   x=Cd([rn.randrange(11) for _ in range(96)])
   F=x**3+A*x+B0
   if F.is_square():
    P=f_mu((11**48-1)//16,(x,F.sqrt()),A)
    if P is not None:break
  else:raise AssertionError('points')
  Q=f_ad(applyalpha(Dd,P),ng(f_mu(15,P,A)),A)
  if f_mu(8,Q,A) is not None:
   assert f_mu(16,Q,A) is None and applyalpha(Dd,Q)==f_mu(2,Q,A)
   return Q
 raise AssertionError('16 basis')
# Lift residue torsion by the proven affine Hensel criterion.
def lift_tor(P0,l,A,B):
 x0,y0=P0
 def pt(x):return x,sol(ra(y0),lambda y:(y*y-x**3-A*x-B,2*y))
 def crit(x):
  P=pt(x)
  if l==16:
   X,Y=r_mu(8,P,A);return Y,8*(3*X*X+A)/(2*P[1])
  k=l//2;Q,T=r_mu(k,P,A),r_mu(k+1,P,A)
  return T[0]-Q[0],((k+1)*T[1]-k*Q[1])/P[1]
 x=sol(ra(x0),crit);P=pt(x)
 assert crit(x)[0]==0 and (P[0].mod(),P[1].mod())==P0
 return P
def bi(A):
 L=[R(1)]
 for x in A:L.append(L[-1]*x)
 b=L[-1].inv();Li=[]
 for j in reversed(range(len(A))):
  Li.append(b*L[j]);b=b*A[j]
 return Li[::-1]
def kerx(P,A):
 x,y=P
 Q=r_ad(P,P,A);J=(*Q,R(1))
 Xs=[x,J[0]];Zs=[J[2],J[2]]
 for _ in range(3,121):
  X,Y,Z=J;ZZ=Z*Z
  U=x*ZZ;S=y*Z*ZZ
  h=U-X;rr=2*(S-Y)
  HH=h*h;I=4*HH;K0=h*I;W=X*I
  XX=rr*rr-K0-2*W
  J=XX,rr*(W-XX)-2*Y*K0,2*Z*h
  Xs.append(XX);Zs.append(J[2])
 u=bi(Zs)
 return [X*y*y for X,y in zip(Xs,u)]
def vel(A,B,KX,sgn):
 SS=[x*x*x+A*x+B for x in KX]
 uu=1-sgn*len(KX)
 a=A-5*sgn*sum(3*x*x+A for x in KX)
 b=B-7*sgn*sum(5*x*x*x+3*A*x+2*B for x in KX)
 S=-2*sgn*sum(KX)
 def g(T):
  x,y=T;xf=x*x*x+A*x+B;f1=3*x*x+A
  vs=bi([x-k for k in KX])
  U=uu*x+S;J=R(uu)
  for kf,v in zip(SS,vs):
   v2=v*v;w=xf+kf
   U+=sgn*w*v2
   J+=sgn*(f1-2*w*v)*v2
  V=y*J
  assert V*V==U*U*U+a*U+b
  return U,V
 return a,b,g
def t8(P,A):return E0['t8'](P,A)
def t16(P,A,B):
 a0=t8(r_mu(2,P,A),A)
 A1,B1,F=vel(A,B,[r_mu(8,P,A)[0]],1)
 a1=t8(F(P),A1)
 t=(a1-2*a0)/(a0+4)
 assert t*t/(t+2)==a0 and t*(t+4)==a1
 return t
def c2(Q):
 X,Y=Q
 A=(Y+X**4+1)/2
 if X==0 or A==0:return None
 return X-2+3*X/A,(A-2*X-1)/X
def jff(v):
 for k in (2,4,16):
  if v+k==0:return None
  v=v*v/(v+k)
 if v==0:return None
 return (v+256)**3/(v*v)
ff=Z['base'];chart0={}
for X in ff:
 for Y in ff:
  if Y*Y!=X**8+14*X**4+1:continue
  U=c2((X,Y))
  if U and jff(U[0]) in (Cd(0),Cd(1728)):
   assert cod(U) not in chart0
   chart0[cod(U)]=(X,Y)
def lift_chart(t,v):
 XY=chart0[cod((t.mod(),v.mod()))];X,Y=map(ra,XY)
 for _ in range(K.bit_length()+1):
  xx=X*X;xxxx=xx*xx;Gm=Y+xxxx+1;W=t+2-X
  f=Y*Y-xxxx*xxxx-14*xxxx-1;g=W*Gm-6*X
  if f==g==0:break
  fx=-8*xxxx*xx*X-56*xx*X;fy=2*Y
  gx=4*xx*X*W-Gm-6;gy=W
  dt=(fx*gy-fy*gx).inv()
  X,Y=X-(f*gy-fy*g)*dt,Y-(fx*g-f*gx)*dt
 assert Y*Y==X**8+14*X**4+1
 A=(Y+X**4+1)/2
 assert (X-2+3*X/A,(A-2*X-1)/X)==(t,v)
 return X,Y
# Two-coordinate arithmetic for the 160 actual fixed factors.
def ba(a,b):return (a[0]+b[0])%M,(a[1]+b[1])%M
def bm(a,b):return (a[0]*b[0]+2*a[1]*b[1])%M,(a[0]*b[1]+a[1]*b[0])%M
def bs(a,b):return (a[0]-b[0])%M,(a[1]-b[1])%M
def sc(n,a):return n*a[0]%M,n*a[1]%M
def bp(a,n):
 t=(1,0)
 while n:
  if n&1:t=bm(t,a)
  a=bm(a,a);n//=2
 return t
def binv(a):
 c=pow((a[0]**2-2*a[1]**2)%M,-1,M)
 return (c*a[0])%M,(-c*a[1])%M
tt=(1,0)
def w3(P):
 X,Y=P;xx=binv(X)
 return sc(-1,xx),sc(-1,bm(Y,bp(xx,4)))
def w48(P):
 X,Y=P;xx=binv(bs(X,tt))
 return bm(ba(X,tt),xx),sc(4,bm(Y,bp(xx,4)))
def bb(P):
 X,Y=P;a=ba(Y,bp(X,4));b=ba(a,(7,0))
 return [tt,a]+[bm(bp(X,i),b) for i in range(1,5)]
def tw(K,x,y):
 v=ba((2,0),sc(2,ba(x[5],y[5])))
 v=ba(bs(v,sc(2,bm(x[1],y[1]))),sc(2,bm(x[3],y[3])))
 return bs(bs(v,bm(x[2],y[4])),bm(x[4],y[2])) if K==5 else bs(bs(v,bm(x[2],y[2])),bm(x[4],y[4]))
def val(P):
 def f(x):
  if not x:return K
  d=0
  while x%11==0:d+=1;x//=11
  return d
 return min(map(f,P))
WG=[(l,xy,ep,[tuple(dec(t if isinstance(t,R) else R(t))) for t in b]) for l,xy,ep,b in E0['WG']]
def uv(X,Y):
 P=(tuple(dec(X)),tuple(dec(Y)))
 xs=[bb(x) for x in [P,w48(w3(P)),w3(P),w48(P)]]
 z=0;mx=0
 for j,_,w,B0 in WG:
  v=[val(tw(j,B0,x)) for x in xs]
  if max(v)==K:return None,K
  z+=w*(v[0]+v[1]-v[2]-v[3]);mx=max(mx,max(v))
 return z,mx
# Snapshot and exact transports of all residue basis points and endomorphisms.
rho=E1['Al'][0]; cx=E1['x'];CR=E1['R'];rem=E1['rem']
A,B0=OA,Cd(0); snapshots=[]
for j,(k0,*_) in enumerate(L['horizontal_cycle']):
 k=Cd(int(k0[0]))+int(k0[1])*B
 snapshots.append((A,B0,sP,sQ,s3,crop(rho)))
 # Exact rational function pull through the same normalized isogeny.
 k1=E1['F'](int(k0[0]))+int(k0[1])*E1['s']
 a1,a2=L['horizontal_cycle'][j][1]
 b=3*k1*k1+E1['F'](a1%11)+(a2%11)*E1['s']
 r=rho.sub(cx+k1)-k1; z=r+b/r
 a0,a1=rem(z.x,b);b0,b1=rem(z.y,b);assert a0*b1==a1*b0
 rr=CR(a0,b0) if b0 else CR(a1,b1)
 rho=rr.sub(cx-k1)+k1
 A,B0,ph=f_ve(A,B0,[(k,Cd(0))])
 sP,sQ,s3=ph(sP),ph(sQ),ph(s3)
 assert sP is not None and sQ is not None and s3 is not None
def onevertex(g,cut=242):
 t=time.monotonic()
 fa,fb,P0,Q0,T3,Dd=snapshots[g]
 A,B0=map(enc,L['horizontal_cycle'][g][1:3])
 assert (A.mod(),B0.mod())==(fa,fb)
 assert applyalpha(Dd,T3) is None
 T16=choose16(fa,fb,Dd)
 T16=lift_tor(T16,16,A,B0);T3=lift_tor(T3,3,A,B0)
 P,Q=lift_tor(P0,241,A,B0),lift_tor(Q0,241,A,B0)
 vq=[None,Q]
 for j in range(2,121):vq.append(r_ad(vq[-1],Q,A))
 vq=vq+[ (t[0],-t[1]) for t in vq[120:0:-1] ]
 assert len(vq)==241
 out=[]
 for a,b in DIR[:cut]:
  P1=r_ad(P,vq[b],A) if a else Q
  KX=kerx(P1,A)
  aa,bb0,ph=vel(A,B0,KX,2)
  P16=ph(T16);P3=ph(T3)
  t1=t16(P16,aa,bb0)
  a3,b3,f3=vel(aa,bb0,[P3[0]],2)
  t2=t16(f3(P16),a3,b3)
  X,Y=lift_chart(t1,t2)
  z,mx=uv(X,Y)
  if (g,a,b) in ((0,1,0),(0,0,1)):
   expected=E0['out'][0 if a else 1]
   assert dec(X)==expected['X'] and dec(Y)==expected['Y']
   assert z==expected['raw_U_valuation']
  out.append([a,b,z,phase(a,b),mx])
 print('exact vertex',g,'arcs',cut,'resolved',sum(z is not None for _,_,z,_,_ in out),'secs',round(time.monotonic()-t,2),file=sys.stderr)
 return out
if __name__=='__main__':
 a=int(sys.argv[1])
 assert 0<=a<19 and len(sys.argv)==2
 out=onevertex(a,242)
 assert all(z is not None and m<K for _,_,z,_,m in out)
 print(json.dumps(out,separators=(',',':')),flush=True)
 # FLINT contexts imported via independently sealed runpy replays have a
 # destructor ordering issue. Use a dedicated child process and terminate it
 # only after every asserted output has been flushed. Exceptions before this
 # point still fail the worker, and the parent compares its complete output.
 sys.stderr.flush()
 os._exit(0)
