"""Four literal odd theta cells and exact rational reconstruction of the same Gamma."""
from itertools import product
from math import gcd,isqrt,prod
from pathlib import Path
import json
B=204618888056724185
PR=(5,11,17,163,661,733,1489,1861)
TH=(131,6551,2470991,16782959)
L=prod(TH); H=isqrt((L-1)//2)
assert B==prod(PR)
D=Path(__file__).resolve().parent
P=D.parent/"ct-original-scalar-kummer-fiber-r1"/"PINNED-SCALAR-FIBER.json"
S=json.loads(P.read_text());h,J,R,N=(S[k] for k in ("h","J","R_input","N"))
def normchar(x,p):
 r=pow(x%p,(p-1)//2,p)
 return -1 if r==p-1 else r
def source_mod(p):
 if p==7: # Singular source arm: use the separately checked literal p=7 row.
  return dict(p=7,delta=6,c=1,chart_cases=None)
 if (1+114444*R)*R%p==0:return
 sq2=next((j for j in range(p) if j*j%p==2%p),None)
 bs= (None,) if sq2 is None else (sq2,-sq2)
 bv=[]
 for k in bs:
  def k0(a,b=0):return (a%p,b%p) if k is None else ((a+b*k)%p,0)
  def add(x,y):return ((x[0]+y[0])%p,(x[1]+y[1])%p)
  def sub(x,y):return ((x[0]-y[0])%p,(x[1]-y[1])%p)
  def mul(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%p,(x[1]*y[0]+x[0]*y[1])%p)
  def sq(x):return mul(x,x)
  def div(x,y):
   n=pow((y[0]*y[0]-2*y[1]*y[1])%p,-1,p)
   return mul(x,(y[0]*n%p,-y[1]*n%p))
  z=k0(0);ad=sq(k0(3,-1));base=(k0(1,1),k0(0,2))
  def cc(Pt):return Pt is None or sq(Pt[1])==mul(Pt[0],sub(sq(Pt[0]),ad))
  assert cc(base)
  def comb(Pt,Qt):
   if Pt is None:return Qt
   if Qt is None:return Pt
   x,y=Pt;u,v=Qt
   if x==u:
    if add(y,v)==z:return None
    assert y==v
    m=div(sub(mul(k0(3),sq(x)),ad),mul(k0(2),y))
   else:m=div(sub(y,v),sub(x,u))
   X=sub(sub(sq(m),x),u)
   Y=sub(mul(m,sub(x,X)),y)
   assert cc((X,Y))
   return X,Y
  def times(n):
   P=None
   for b in bin(n)[2:]:
    P=comb(P,P)
    if b=='1':P=comb(P,base)
   return P
  a=sum(-normchar(x**3-x,p) for x in range(p))
  if k is None:
   a=a*a-2*p
   q=p*p
  else:q=p
  order=(q+1+a)*(q+1-a)
  assert times(order) is None,(p,k,a,base,order)
  hh=h%order;ii=(pow(6,15,order)*pow(3,N,order)*J)%order
  def chart(n):
   P=times(n)
   if P is None:return
   x,y=P;d=add(sq(x),ad)
   if d==z:return
   return div(mul(k0(2),y),d)
  U,V=chart(hh),chart(ii)
  if U is None or V is None:return
  bv.append((U,V,order))
 if sq2 is None:
  U,V,_=bv[0]
  nrm=lambda r:(r[0]**2-2*r[1]**2)%p
  h0,i0,f=nrm(U),nrm(V),(U[0]**2+2*U[1]**2)%p
 else:
  (up,vp,_),(un,vn,_)=bv
  h0,i0,f=up[0]*un[0]%p,vp[0]*vn[0]%p,(up[0]**2+un[0]**2)*pow(2,-1,p)%p
 if not h0:return
 Qa=i0*pow(h0*pow(R,15,p),-1,p)%p
 Nb=(1+(h0*pow(R,-1,p))**2+2*f*pow(R,-1,p))%p
 W=(Nb**2+R*Qa**2)%p
 c=12*W*pow(1+114444*R,-1,p)%p
 delta=(1-B*c*c)%p
 return dict(p=p,delta=delta,c=c,W=W,chart_cases=bv)
def sqrt_mod(p,a):
 if p%4==3:
  x=pow(a,(p+1)//4,p)
  assert x*x%p==a%p;return x
 for x in range(1,p):
  if x*x%p==a%p:return x
 raise ValueError((p,a))
def rat_recon(r,h=H):
 aa,bb=L,r
 xa,xb=0,1
 while bb>h:
  q=aa//bb
  aa,bb=bb,aa-q*bb
  xa,xb=xb,xa-q*xb
 if not bb or not xb or abs(xb)>h or gcd(bb,xb)>1:return
 return (bb if xb>0 else -bb,abs(xb))
def build_roots():
 roots=[]
 for p in TH:
  a,b=sqrt_mod(p,B),sqrt_mod(p,5)
  s=sorted({i*a*(2+j*b)%p for i in (1,-1) for j in (1,-1)})
  assert len(s)==4 and all((x**4-18*B*x*x+B*B)%p==0 for x in s)
  roots.append(s)
 return roots
def run():
 roots=build_roots(); cs=[(L//p)*pow(L//p,-1,p) for p in TH]
 rs=sorted({sum(a*b for a,b in zip(cs,l))%L for l in product(*roots)})
 assert len(rs)==256
 cuts=[]
 for p in (7,43,83,101,109,139,151,167,197,211,223,227,229):
  a=source_mod(p)
  assert a is not None and a['delta']
  cuts.append(a)
 assert cuts[0]['p']==7 and cuts[0]['c']==1 and cuts[0]['delta']==6
 ac=[]
 steps=[0]*(len(cuts)+1)
 for d in sorted(map(prod,([p for p,i in zip(PR,m) if i] for m in product(range(2),repeat=8)))):
  if d*d>B:continue
  e=B//d
  ds=pow(d,-1,L)
  for a in rs:
   r=rat_recon(a*ds%L)
   if r is None:continue
   x,y=r
   if x<=0 or gcd(d*x,y)!=1 or gcd(e,x)!=1:continue
   f=(d*x*x)**2-18*B*x*x*y*y+(e*y*y)**2
   if f<=0:continue
   steps[0]+=1
   for i,cut in enumerate(cuts,1):
    ch=normchar(f*cut['delta'],cut['p'])
    if ch==-1:break
    steps[i]+=1
   else:ac.append((d,x,y,f))
 assert steps==[6110,1538,610,372,191,109,49,22,12,7,5,3,2,0] and not ac
 # Algebraic calibration (synthetic beta, not the original scalar).
 from fractions import Fraction as F
 beta,delta=29,F(1,20)
 u,A,b=F(15),F(29),F(7)
 K=delta*A/beta;Ht=delta*b;Z=delta*u
 r=K/(Z+2*Ht);ss=(1-beta*r*r)/Ht;x=beta*r*r
 assert 1-18*x+x*x==delta*ss*ss
 t=4*beta*r/(1-x);tp=2*beta*r/(1+x)
 w=beta**2*delta*ss*(3+x)*(1+3*x)/((1-x)*(1+x)**2)
 fs=lambda t:(t*t-beta)*(t*t+3*beta)
 assert t==A/b and tp==A/u and w*w==delta*fs(t)*fs(tp)
 print(json.dumps(dict(calibration=[str(x) for x in (r,ss,t,tp,w)],beta=B,theta_known=TH,visible_product=L,balance_height_cut=H,
                        local_residue_sets=roots,cuts=cuts,local_prefix_counts=steps, survivors=ac),
                  indent=2,sort_keys=True))
if __name__=='__main__':run()
