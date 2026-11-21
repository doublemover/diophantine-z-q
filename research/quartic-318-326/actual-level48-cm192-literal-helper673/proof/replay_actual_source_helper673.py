#!/usr/bin/env python3
"""One literal source cell, no scan, actual norm or Heegner coefficient."""
import json, math, re
from hashlib import sha256
from pathlib import Path
from fractions import Fraction as F
from functools import reduce
from operator import mul
here=Path(__file__).resolve().parent
raw=(here/'PINNED-ORIGINAL-A0-SCALAR-AND-LABEL-PREFIX.json').read_bytes()
assert sha256(raw).hexdigest()=='5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7'
a=json.loads(raw); S=1+6**15*3**65536*int(a['J']); k=2*(S-2)
defs=(here/'LITERAL-GATE-EXPRESSIONS-118-138.txt').read_text()
d={}
for i,t in re.findall(r'def value(\d+) \(w : Assignment\) : ℚ := (.*)',defs):
 t=re.sub(r'w (\d+)',r'w[\1]',t)
 t=re.sub(r'value(\d+) w',r'w[\1]',t)
 t=re.sub(r'(-?\d+) / (\d+)',r'F(\1,\2)',t)
 d[int(i)]=compile(t,'lea','eval')
assert len(d)==21

def labels(N):
 g=math.gcd(S-2,N)
 while math.gcd((S-2)//g,N)>1:g*=math.gcd((S-2)//g,N)
 M=N*g; x,y=0,1; z=S%M
 for bit in bin(k)[2:]:
  A=x*(2*y-z*x)%M; B=(y*y-x*x)%M
  x,y=(A,B) if bit=='0' else (B,(z*B-A)%M)
 assert x%g==0
 return [3723%N,S%N,y%N,(x//g)*pow((S-2)//g,-1,N)%N]

roots=[F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
def data(p):
 def inv(x):return pow(x%p,-1,p)
 def rat(x):x=F(x);return x.numerator*inv(x.denominator)%p
 def ar(x):return x%p
 def chi(m):return {1:1,0:0,p-1:-1}[pow(m%p,(p-1)//2,p)]
 assert chi(2)==1 and p%24==1 and chi(17)==-1
 r=next(t for t in range(p) if t*t%p==2)
 def mk(z):
  D=(3-z)**2%p; P=(ar(1+z),ar(2*z))
  def ec(P,Q):
   if P is None:return Q
   if Q is None:return P
   x,y=P;u,v=Q
   if x==u:
    if ar(y+v)==0:return None
    w=ar((3*x*x-D)*inv(2*y))
   else:w=ar((v-y)*inv(u-x))
   a=ar(w*w-u-x);b=ar(w*(x-a)-y)
   assert b*b%p==(a*a*a-D*a)%p
   return a,b
  X=[None,P]
  while (W:=ec(X[-1],P)) is not None:X.append(W)
  def cv(j):
   P=X[j%len(X)]
   if P is None:return 0,1
   x,y=P
   den=inv(x*x+D)
   return ar(2*y*den),ar((x**4-6*D*x*x+D*D)*den*den)
  return len(X),D,cv
 g1,D1,f1=mk(r);g2,D2,f2=mk(-r)
 N=math.lcm(g1,g2);ls=labels(N)
 def coords(x,y):return ar((x+y)*inv(2)),ar((x-y)*inv(2*r))
 scales=[]
 for f in (f1,f2):
  try:scales.append(reduce(lambda a,n: ar(-a*inv(f(n)[0])),ls,1))
  except ValueError:return dict(p=p,r=r,orders=[g1,g2],labels=ls,error='fixed scale charts')
 G=coords(*scales)[0];nr=ar(scales[0]*scales[1])
 c=[1,ar(G+nr),nr]
 if not all(c):return dict(p=p,r=r,orders=[g1,g2],labels=ls,scales=c,error='fixed scale zero')
 rs=[rat(x) for x in roots]
 tt=[t for t in range(p) if all(chi(t-z)==-1 for z in rs) and
     all((cc*cc*t-1)%p and all((cc*cc*t-z)%p for z in rs) for cc in c)]
 if not tt:return dict(p=p,r=r,orders=[g1,g2],labels=ls,scales=c,error='all contact windows empty')
 def proof(h):
  class Fail(ValueError):pass
  us=[];vs=[];prs=[];ars=[];vs2=[]
  for z,D,f in [(r,D1,f1),(-r,D2,f2)]:
   U,V=f(h); kc=rat(-1+F(7,4)*z); m=rat(F(39,8)-F(9,2)*z)
   if not U:raise Fail('U(h)')
   sh=ar((kc*V*inv(U)-m)*inv(kc*kc+D*U*U))
   mid=U*U*sh%p; fv=mid*sh%p; arg=D*fv*fv%p
   A=ar(m+kc*kc*sh+D*mid); B=ar(kc*kc+m*sh+D*fv)
   PG=ar(1-rat(F(61,65))*arg+rat(F(16,195))*arg*arg)
   QG=ar(1-rat(F(7,13))*arg)
   cm=ar(kc*sh*PG*inv(QG)*inv(B))
   if not cm:raise Fail('common')
   l=[f(n*h) for n in ls]
   rr=[f(n*(h-1)) for n in ls]
   prs.append([ar(u*A*inv(kc*v)) for u,v in l])
   al=[]
   for j,(u,v) in enumerate(rr):
    x=v-1
    pp=ar(1-x*inv(5)) if j==0 else ar((1+rat(F(12,65))*x-rat(F(2,195))*x*x)*inv(1+rat(F(5,13))*x))
    al.append(ar(-u*pp*inv(cm)))
   ars.append(al)
   us.append([U]+[u for u,v in l+rr]);vs.append([V]+[v for u,v in l+rr]);vs2.append(fv)
  UU=list(map(lambda x:coords(*x),zip(*us))); VV=list(map(lambda x:coords(*x),zip(*vs)))
  actual_guards=[ar(UU[5+j][0]**2+2*UU[5+j][1]**2-UU[1+j][0]**2-2*UU[1+j][1]**2) for j in range(4)]
  assert all(actual_guards)
  w={0:0,37:ar(us[0][0]*us[1][0])}
  for j in range(8):
   w[4*j+1],w[4*j+2]=UU[j+1]
   w[4*j+3],w[4*j+4]=VV[j+1]
  for j,(x,y) in enumerate(UU[1:5]):
   w[58+2*j]=ar((x*x+2*y*y)*(inv(2) if j==2 else 1))
   w[59+2*j]=ar(x*y)
  g=coords(*vs2)
  w[90]=ar(g[0]*g[0]+2*g[1]*g[1]);w[91]=ar(g[0]*g[1])
  for j,(pair1,pair2) in enumerate(zip(zip(*prs),zip(*ars))):
   w[102+4*j],w[103+4*j]=coords(*pair1)
   w[104+4*j],w[105+4*j]=coords(*pair2)
  for j in range(118,139):
   w[j]=rat(eval(d[j],{'w':w,'F':F,'__builtins__':{}}))
  # ActualDetectorFold318 exactly 16 values and corresponding exponents.
  leaves=[(7,w[126],0),(1,w[125],0),(1,w[58],2*w[59]),(1,w[60],2*w[61]),(1,2*w[62],2*w[63]),(1,w[64],2*w[65])]
  leaves += [(1,w[i]-1,-w[i+1]) for i in [19,23,27,31]]
  leaves += [(7,w[127],2*w[128]),(25,w[129],2*w[130]),(25,w[131],2*w[132]),(25,w[133],2*w[134])]
  leaves += [(7,110885832*w[0]-7446*w[102]+110885832*w[118]+221771664*w[135]+13860729,-7446*w[103]-29784*w[136]),(25,-2*w[123]+w[137]+1,-4*w[124]+4*w[138])]
  leaves=[(e,ar(x),ar(y)) for e,x,y in leaves]
  assert len(leaves)==16
  def fold(t,cc):
   T=ar(cc*cc*t);DL=ar(T-1);Ft=math.prod(T-z for z in rs)%p
   b=ar(pow(cc,10,p)*DL*DL*inv(Ft))
   ws={1:b,7:ar(b**7*DL**18),25:ar(pow(b,25,p)*pow(DL,72,p))}
   x,y=1,0
   for e,i,j in leaves:x,y=ar(x*x+2*y*y+ws[e]*i),ar(2*x*y+ws[e]*j)
   tau=ar((x*x-2*y*y)*inv(2*x))
   B=ar(tau*tau*Ft*inv(pow(cc,10,p)*DL**6))
   return x,y,tau,B,ar(1-B*inv(17))
  rows=[]
  for t in tt:
   try:
    ff=[fold(t,cc) for cc in c]
    if all(f[2] for f in ff) and chi(ff[0][4])==1:
     rows.append([t,ff])
   except ValueError:pass
  return rows,leaves,actual_guards
 h=int(a['h'])%N
 rows,l,guards=proof(h)
 qstar=next(q for q in range(1,p) if chi(q)==-1)
 out=[]
 for t,folds in rows:
  if t!=61:continue
  contact=[[chi(cc*cc*t-z) for z in rs] for cc in c]
  assert contact[0]==[-1]*5 and all(all(r) for r in contact)
  # The shape of normalized rows: Q*D is a unit and its square scales every norm.
  qstar_contact_norms=[[ar(qstar*(t-z*inv(cc*cc))) for z in rs] for cc in c]
  assert all(all(r) for r in qstar_contact_norms)
  assert all(chi(r)==1 for r in qstar_contact_norms[0])
  out.append([t,folds,l,guards,contact,qstar_contact_norms])
 return dict(p=p,r=r,orders=[g1,g2],N=N,labels=ls,scales=c,fixed_anchor_unit=bool(int(a['J'])%p),
             h_fixed=h,h_cells_checked=[h],qstar=qstar,rows=out,
             scope="retained actual a=0 source at I=673, not a numerical linear key or mark")
ans=data(673)
assert ans["orders"]==[314,314] and ans["h_fixed"]==290 and ans["labels"]==[269,107,313,307]
assert ans["fixed_anchor_unit"] and pow(17,336,673)==672 and 145**2%673==162
res=lambda x: x.numerator*pow(x.denominator,-1,673)%673
roots_by_scale=[[res(x/F(c*c)) for x in roots[1:]] for c in ans["scales"]]
assert len({x for row in roots_by_scale for x in row})==12
assert all(x for row in roots_by_scale for x in row)
ans["distinct_nonzero_contact_roots"]=roots_by_scale
ans["square_root_of_delta190"]=145
assert ans["scales"]==[1,293,123] and ans["h_cells_checked"]==[290] and len(ans["rows"])==1
assert ans["rows"][0][0]==61
assert [list(v[3:]) for v in ans["rows"][0][1]]==[[628,162],[84,194],[472,92]]
print(json.dumps(ans,sort_keys=True,indent=2))
