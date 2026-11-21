from pathlib import Path
from fractions import Fraction as Q
from math import gcd,prod
from sympy import primerange
from flint import fmpz
isprime=lambda x:fmpz(x).is_probable_prime()
import json,sys
from hashlib import sha256
p=(Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py')
assert sha256(p.read_bytes()).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(compile(p.read_text().split('\nqs=(')[0].replace('Path(__file__).resolve().parent.parent','Path('+repr(str(p.parent.parent))+')'),str(p),'exec'))
x=json.load(open(root/'linked-detector-numeric-anchor-phase-repair-r1'/'EXACT-PRIMARY-REPAIRED-COVER.json'))
a,b=x['a'],x['b'];X,Y,Z=4619710060,41,38613147
assert X*X-b*Y*Y==2399*Z*Z
pa=415721
T=Q(1,2399)
W0,Y0=Q(X,2399*Z),Q(Y,2399*Z)
Pmod=17
Tsmall=[(2,600),(3,8),(5,4),(7,4),(11,4),(17,1),(19,4),(23,4),(37,4),(2399,4)]
cells=[(p,w) for p,w,_,_ in x['old_cells_W_a_unit_b_unit']]
cells += [(c['p'],c['W_mod_p2']) for c in x['actual_new_contacts'][1:]]
assert len(cells)==18
def Dn(u,v):return 2399*Z*(v*v-b*u*u)
def coords(u,v):
 d=Dn(u,v)
 return (Q(X*(v*v+b*u*u)+2*b*Y*u*v,d),Q(Y*(v*v+b*u*u)+2*X*u*v,d))
def sqrt2(a,k):
 a=mod(a,1<<k);assert a%8==1
 x=1
 for j in range(3,k):
  if (x*x-a)%(1<<(j+1)):x+=1<<(j-1)
 assert (x*x-a)%(1<<k)==0
 return x
local=[]
for p,m in Tsmall+[(p,0) for p,_ in cells]:
 W=Q(1,p**m) if m else Q(dict(cells)[p])
 scale=p**m
 tu=(W*W-T)*scale**2/b
 # At known b-support T difference has depth1, as does b; tu is then a unit.
 assert vp(tu,p)==0
 prec=2*m+40 if m else 12
 ys=(sqrt2(tu,prec),) if p==2 else rootsmod(mod(tu,p**prec),p,prec)
 for yy in (*ys,*[-z for z in ys]):
  Yp=Q(yy,scale)
  u=2399*(Yp*W0-W*Y0)
  v=1+2399*(W*W0-b*Yp*Y0)
  if not v:continue
  P=u/v; A,C=P.numerator,P.denominator
  W1,Y1=coords(A,C)
  if (m and vp(W1,p)!=-m) or (not m and vp(W1-W,p)<2):continue
  break
 else:raise ValueError(('no conic precision',p,m))
 d=vp(Dn(A,C),p)
 k=(d-m+1 if m else d+2)
 # Preserve all numerator/denominator depths if negative W, not just quotient sign.
 if m:k=max(k,d+1)
 k=max(k,1)
 local.append((p,k,A%p**k,C%p**k))
def gauss(u,v):
 norm=lambda X:X[0]*X[0]+X[1]*X[1]
 while True:
  if norm(u)>norm(v):u,v=v,u
  nu=norm(u);uv=sum(x*y for x,y in zip(u,v));n=(2*uv+nu)//(2*nu)
  if not n:return u,v
  v=tuple(y-n*x for x,y in zip(u,v))
det=1
w,z=(1,0),(0,1)
for p,k,A,C in local:
 N=p**k; det*=N
 d=(C*w[0]-A*w[1])%N;e=(C*z[0]-A*z[1])%N
 if d%p==0:w,z=z,w;d,e=e,d
 assert d%p
 v=e*pow(d,-1,N)%N
 w,z=gauss(tuple(N*y for y in w),tuple(y-v*x for x,y in zip(w,z)))
L=isqrt(b); K=max(1,L//100)
ww,zz=gauss((K*w[0],w[1]-L*w[0]),(K*z[0],z[1]-L*z[0]))
assert ww[0]%K==zz[0]%K==0
w=(ww[0]//K, ww[1]+L*(ww[0]//K))
z=(zz[0]//K, zz[1]+L*(zz[0]//K))
assert abs(w[0]*z[1]-w[1]*z[0])==det
for p,k,A,C in local:
 assert all((C*x-A*y)%p**k==0 for x,y in (w,z))
print('lattice',det.bit_length(),'basis',[[v.bit_length() for v in u] for u in (w,z)],'local',[(p,k) for p,k,_,_ in local],flush=True)
N=int(sys.argv[1]) if len(sys.argv)>1 else 120
tiny=list(primerange(2,600))
Psmall=prod(p for p,k,A,C in local)
nt=[0]*4;res=[]
for i in range(0,N+1):
 for j in range(-N,N+1):
  if (i==0 and j<=0) or gcd(i,j)!=1:continue
  u,v=tuple(x*i+y*j for x,y in zip(w,z))
  if gcd(gcd(u,v),Psmall)!=1:continue
  Wn=X*(v*v+b*u*u)+2*b*Y*u*v
  Wd=Dn(u,v)
  if Wd<0:Wd,Wn=-Wd,-Wn
  if Wn<=2*Wd:continue
  zc=gcd(Wn,Wd);Wn//=zc;Wd//=zc
  assert Wd%407==0
  q,r=divmod(Wn*Wn+32*(Wd*Wd//407),pa)
  assert r==0
  nt[0]+=1
  sq=1
  for p in tiny:
   h=0
   while q%p==0:q//=p;h+=1
   if h%2:break
   if h:sq*=p**(h//2)
  else:
   nt[1]+=1
   if q%8!=1 or not fmpz(q).is_probable_prime():continue
   nt[2]+=1
   W,Yp=coords(u,v)
   assert all(vp(W,p)==-m for p,m in Tsmall)
   assert all(vp(W-Q(r),p)>=2 for p,r in cells)
   assert W*W-Q(-32,407)==Q(pa*q*sq*sq,W.denominator**2)
   assert W*W-b*Yp*Yp==T
   R=dict(i=i,j=j,parameter=[u,v],W=[W.numerator,W.denominator],
          Y=[Yp.numerator,Yp.denominator],qa=q,qa_bits=q.bit_length(),cofactor_square_root=sq,
          b=b,pa=pa)
   print('hit',json.dumps(R),flush=True)
   res.append(R);nt[3]+=1
print('counts',nt,flush=True)
Path(f'/tmp/joined-W-fixed-b-fastint-{N}.json').write_text(json.dumps(dict(b=b,lattice_basis=[w,z],lattice_det=det,local=local,cells=cells,counts=nt,hits=res),indent=2))
