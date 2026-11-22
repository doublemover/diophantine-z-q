import json
from math import gcd,isqrt
import pilot_ladder as m
p=29
f=m.F0;E=[(a,b) for a,b in __import__('itertools').product(range(p),repeat=2)]
enc=lambda x:f.c(*x)
dec=f.residue
a=lambda x,y:dec(f.ad(enc(x),enc(y)))
s=lambda x,y:dec(f.su(enc(x),enc(y)))
z=lambda n:(n%p,0)
mu=f.bmul
pw=f.basepow
div=lambda x,y:mu(x,pw(y,839))
D={}
def deps(k,t):
 ab=(16,16) if k==4 else (4,8) if k==8 else (2,4)
 c,d=ab
 if a(t,z(c))==(0,0):return None
 return div(mu(t,t),a(t,z(c))),mu(t,a(t,z(d)))
for k in (4,8,16):
 for t in E:
  lr=deps(k,t)
  if lr:D.setdefault((k,*lr),[]).append(t)
def levels(row,k):
 ns=[]
 for x,y in zip(row,row[1:]):
  vv=D.get((k,x,y),[])
  assert len(vv)==1
  ns.append(vv[0])
 return ns
rt={}
for y in E:rt.setdefault(mu(y,y),[]).append(y)
C={}
for X in E:
 if X==z(0):continue
 X4=pw(X,4)
 for Y in rt.get(a(a(pw(X4,2),mu(z(14),X4)),z(1)),[]):
  B=div(a(a(Y,X4),z(1)),z(2))
  if B==z(0):continue
  A16=a(s(X,z(2)),div(mu(z(3),X),B))
  B16=div(s(s(B,mu(z(2),X)),z(1)),X)
  C.setdefault((A16,B16),[]).append((X,Y))
if __name__=='__main__':
 start,r2,r3,c2,c3=m.genp();Ladd=[];Ts=[]
 for j in range(3):
  if j:start,_=m.step(*start,3,3-j)
  row=start;T=[];T4=[]
  for k in range(8):
   row,(q,q4)=m.step(*row,2,8-k);T.append(q)
   if q4 is not None:T4.append(q4)
  for k,q4 in enumerate(T4):assert deps(4,q4)==(T[k],T[k+1])
  Ts.append((T,T4))
  Ladd.append(levels(levels(T4,8),16))
 qlist=[]
 for j in range(2):
  for k in range(5):
   out=C.get((Ladd[j][k],Ladd[j+1][k]),[])
   assert len(out)==1
   qlist.append(out[0])
 def phi(X,Y):
  t=s(X,pw(X,839));w=div(Y,mu(X,X))
  x=div(a(a(w,mu(t,t)),z(2)),z(2));y=mu(t,x)
  return x,y
 Q=None
 # E0 short coordinates U=x−2/3 and short A=−13/3,B=−70/27.
 shift=div(z(2),z(3))
 A=f.c(*div(z(-13),z(3)))
 vals=[]
 for XY in qlist:
  x,y=phi(*XY);vals.append((x,y))
  Q=m.ap(Q,m.lift((s(x,shift),y),f),A,f)
 def long(T):
  return None if T is None else (a(dec(T[0]),shift),dec(T[1]))
 P,fourP=long(Q),long(m.amul(Q,4,A,f))
 assert P==((27,0),(0,16)) and fourP==((17,0),(0,24))
 assert m.amul(Q,36,A,f) is None
 for Q4 in (P,fourP):
  a0,b0=Q4
  assert a0[1]==0 and b0[0]==0 and b0[1]!=0
 assert (52920**2==1344*(1344-119)*(1344+3*119))
 assert 10*10*2%29==(-119)%29
 assert (10*10-7*(7-119)*(7+3*119))%29==0
 # Primitive order and simple binomial irreducibility controls.
 assert m.F2.basepow(m.F2.d,8)==(1,0) and m.F2.basepow(m.F2.d,4)!=(1,0)
 assert m.F3.basepow(m.F3.d,3)==(1,0) and m.F3.d!=(1,0)
 assert pow(841,64,512)==1 and pow(841,32,512)!=1
 assert pow(841,3,9)==1 and pow(841,1,9)!=1
 assert sum(y*y%29==(x**3+1)%29 for x in range(29) for y in range(29))+1==30
 # Enumerate all classes and the order of p2=(2,omega).
 d=-119
 forms=[]
 for a0 in range(1,isqrt((-d)//3)+1):
  for b0 in range(-a0,a0+1):
   v0=b0*b0-d
   if v0%(4*a0):continue
   c0=v0//(4*a0)
   if a0>c0 or gcd(a0,gcd(b0,c0))!=1 or (a0==c0 or abs(b0)==a0) and b0<0:continue
   forms.append((a0,b0,c0))
 def red(a,b,c):
  while True:
   q=(a-b)//(2*a);b,c=b+2*a*q,c+b*q+a*q*q
   if a>c:a,b,c=c,-b,a;continue
   if (a==c or a==abs(b)) and b<0:b=-b
   return a,b,c
 r=0;two=[]
 for k in range(6):
  m0=2**k
  if k and (r*r-r+30)%m0:r+=m0//2
  two.append(red(m0,1-2*r,(r*r-r+30)//m0))
 assert len(forms)==10 and len(set(two[:5]))==5 and two[5]==forms[0] and (3,1,10) not in two
 print(json.dumps(dict(scope="complete oriented inert toy CM orbit, not a literal original detector",
  seed=dict(n=119,reduction_prime=29,zeta=m.ZETA,eigen_roots=[r2,r3],point_seeds=[c2,c3],
  extension_binomials=[m.F2.d,m.F3.d],base_model=[0,1]),
  classes=forms,p2_powers=two,ladder=Ts,t16=Ladd,oriented_labels=qlist,
  phi_values=vals,P=P,fourP=fourP,descended_fourP_mod29=[7,10],rational_sanity_point=[1344,52920]),
  indent=2,sort_keys=True))
