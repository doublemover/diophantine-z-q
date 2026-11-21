from pathlib import Path
from hashlib import sha256
from math import gcd,isqrt,prod
from fractions import Fraction as F
import json,runpy,sys
sys.set_int_max_str_digits(0)
script=(Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py')
assert sha256(script.read_bytes()).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(compile(script.read_text().split('\nqs=(')[0].replace('Path(__file__).resolve().parent.parent','Path('+repr(str(script.parent.parent))+')'),str(script),'exec'))
j=json.load(open(sys.argv[1]))
qa=j['qa'];pa=j['pa'];b=j['b'];a=pa*qa
W=F(*j['W']);Y=F(*j['Y'])
assert W*W-F(-32,407)==F(a*j['cofactor_square_root']**2, W.denominator**2)
assert W*W-b*Y*Y==F(1,2399)
def corn(p):
 x0=sqrtmod(-1,p); r0,r1=p,min(x0,p-x0)
 while r1*r1>p:r0,r1=r1,r0%r1
 r=int(isqrt(p-r1*r1));assert r*r+r1*r1==p
 return (r1,r) if r1%2 else (r,r1)
def capped(G,hh,L):
 while (a:=gcd(G,L))>1 and (b:=a//gcd(a,hh))>1:G//=b
 return G
def add_q(H,r):
 h,T=H;p,mp,mo=r[:3]
 if gcd(mp,mo)>1:raise ValueError('incompatible pair same prime')
 for x,L in ((0,mp),(1,mo),(p**3,p**4)):h,T=crt(h,T,x,L)
 return (h,T)
Bs=json.load(open(root/'linked-detector-numeric-anchor-phase-repair-r1'/'EXACT-PRIMARY-REPAIRED-COVER.json'))
base=crt(h0,L0,204,289)
for d in Bs['actual_new_contacts'][1:]:
 p=d['p']
 for e,m in ((0,d['arms'][0]['order']),(1,d['arms'][1]['order']),(p**3,p**4)):base=crt(*base,e,m)
h,H=base
def odd(n):return n//(n&-n)
def returns(P,n,F,p):
 x,y=P
 A=None
 def dbl(B):
  if B is None:return None
  X,Y,Z=B
  if not Y:return None
  z4=pow(Z,4,p);y2=Y*Y%p
  T=(3*X*X-F*z4)%p
  V=4*X*y2%p
  xx=(T*T-2*V)%p
  yy=(T*(V-xx)-8*y2*y2)%p
  return xx,yy,2*Y*Z%p
 def add(B):
  if B is None:return x,y,1
  X,Y,Z=B
  z2=Z*Z%p
  a=(x*z2-X)%p;b=(y*z2*Z-Y)%p
  if not a:return dbl(B) if not b else None
  a2=a*a%p;a3=a*a2%p
  V=X*a2%p
  xx=(b*b-a3-2*V)%p
  yy=(b*(V-xx)-Y*a3)%p
  return xx,yy,Z*a%p
 for b in bin(n)[2:]:
  A=dbl(A)
  if b=='1':A=add(A)
 return A is None
def options(p,T):
 assert p>0 and p%8==1 and chi(7,p)==-1 and gcd(p,H*Sprod)==1
 A,C=corn(p); Gs=(p+1-2*A,p+1+2*A); gg=gcd(*Gs)
 assert all(gcd(g,p)==1 for g in Gs)
 r=sqrtmod(2,p);N=p*p
 ro=[]
 for x in (r,p-r):
  pt=((1+x)%p,2*x%p);curve=(3-x)**2%p
  f=lambda g:returns(pt,g,curve,p)
  g=min((g for g in Gs if f(g)),default=0)
  assert g 
  CC=[capped(g,z,T) for z in (h,h-1)]
  ws=[f(CC[0]),f(odd(CC[1]))]
  ro.append((x,g,CC[0],odd(CC[1]),ws))
 print('pass scopes',p.bit_length(),(A,C),gg,
       [[x==r,g==Gs[0],cs.bit_length(),co.bit_length(),ws,
         (g//cs).bit_length(),g//co if g//co<2**40 else (g//co).bit_length()] for x,g,cs,co,ws in ro],file=sys.stderr,flush=True)
 return [(p,x[2],y[3],x[0],y[0],A,C) for x,y in (ro,ro[::-1]) if x[4][0] and y[4][1] and gcd(x[2],y[3])==1]
Xr=[]
OA=options(qa,H)
print('available orientations',len(OA),file=sys.stderr,flush=True)
for x in OA:
 try:hj=add_q(base,x)
 except (AssertionError,ValueError):continue
 Xr.append((x,hj))
print('joint compatible',len(Xr),'h sizes',[(h.bit_length(),l.bit_length()) for x,(h,l) in Xr],file=sys.stderr,flush=True)
sys.stdout.write(json.dumps(dict(a=a,b=b,W=j["W"],Y=j["Y"],options=OA,compatible=Xr),indent=2))
