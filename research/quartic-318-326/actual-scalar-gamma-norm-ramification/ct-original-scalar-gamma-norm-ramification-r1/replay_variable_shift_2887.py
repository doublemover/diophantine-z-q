#!/usr/bin/env python3
from pathlib import Path
from math import gcd
import json
# The command may supply a copy of the immutable scalar recipe.
P=Path(__file__).resolve().parent.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json'
S=json.loads(P.read_text())
h,J,R,N=(S[k] for k in ('h','J','R_input','N'))
B=114444*R//(17*12**2);D0=1+114444*R
p=2887;m=p*p
assert all(p%q for q in range(2,54)) and B%p
assert pow(5,(p-1)//2,p)==p-1 and pow(B,(p-1)//2,p)==1
sr=next(i for i in range(p) if i*i%p==2)
sr2=sr+p*((-(sr*sr-2)//p)*pow(2*sr,-1,p)%p)
assert sr2*sr2%m==2
def chars(a,p):
 if a%p==0:return 0
 return 1 if pow(a%p,(p-1)//2,p)==1 else -1
arms=[]
a_sources=[(2805,2480),(2181,204)]
for i,t in enumerate((sr,-sr)):
 e=(3-t)**2%p
 law=lambda x:x*(x*x-e)%p
 a=(1+t)%p,2*t%p
 assert law(a[0])==a[1]**2%p
 count=p+1+sum(chars(law(x),p) for x in range(p))
 assert count==2888
 ix=(pow(6,15,count)*pow(3,N,count)*J)%count
 assert ix==1480
 assert pow(6,15,p)*pow(3,N,p)*J%p==2473
 def add(P,Q):
  if P is None:return Q
  if Q is None:return P
  x,y=P;u,v=Q
  if x==u and (y+v)%p==0:return
  if x==u: slope=(3*x*x-e)*pow(2*y,-1,p)%p
  else:slope=(v-y)*pow(u-x,-1,p)%p
  z=(slope*slope-x-u)%p;w=(slope*(x-z)-y)%p
  assert w*w%p==law(z)
  return z,w
 def times(P,n):
  Q=None
  for dig in bin(n)[2:]:
   Q=add(Q,Q)
   if dig=='1':Q=add(Q,P)
  return Q
 def chart(P):
  x,y=P;return 2*y*pow(x*x+e,-1,p)%p
 q=a_sources[i]
 assert q[1] and q[1]**2%p==law(q[0])
 assert times(q,count) is None and times(a,count) is None
 T=times(q,ix);x,y=T
 deriv=(x**4-6*e*x*x+e*e)%p
 assert deriv and y and (x*x+e)%p
 arms.append(dict(root2=t%p,order=count,source_P0=a,variable_Q=q,shift_Q=T,U=chart(T),
                  U_h_P0=chart(times(a,h%count)),U_i_P0=chart(times(a,ix)),derivative_minus_num=deriv))
assert [s['shift_Q'] for s in arms]==[(497,1059),(1882,1309)]
assert [s['U'] for s in arms]==[1491,1987]
assert [s['U_h_P0'] for s in arms]==[1902,1198]
assert [s['U_i_P0'] for s in arms]==[1904,1189]
def fold(input_Uhsq,input_Uisq,mod):
 a,b=input_Uhsq; u,v=input_Uisq
 H2=a*b%mod
 Np=(1+H2*pow(R*R,-1,mod)+(a+b)*pow(R,-1,mod))%mod
 Q2=u*v*pow(H2*pow(R,30,mod),-1,mod)%mod
 Wp=(Np*Np+R*Q2)%mod; c=12*Wp*pow(D0,-1,mod)%mod
 return dict(delta=(1-B*c*c)%mod,H2=H2,Npack=Np,Q2=Q2,W=Wp,c=c)
hr=[s['U_h_P0']**2%p for s in arms]
true=fold(hr,[s['U_i_P0']**2%p for s in arms],p)
var=fold(hr,[s['U']**2%p for s in arms],p)
assert true['delta']==1634 and var['delta']==0 and var['Npack']==141
H=arms[0]['U_h_P0']*arms[1]['U_h_P0']%p
q=arms[0]['U']*arms[1]['U']*pow(H*pow(R,15,p),-1,p)%p
assert H==753 and q==1295
def Kx(a,e,n):
 # Montgomery-style exact x ladder on y^2=x^3-e*x.
 O=(1,0);T=(a%m,1)
 def db(Q):
  X,Z=Q
  return (X*X+e*Z*Z)**2%m,4*X*Z*(X*X-e*Z*Z)%m
 def ad(P,Q):
  X,Z=P;U,V=Q
  return (X*U+e*Z*V)**2%m,a*(X*V-U*Z)**2%m
 a0,a1=O,T
 for bit in bin(n)[2:]:
  b=ad(a0,a1)
  if bit=='0': a0,a1=db(a0),b
  else:a0,a1=b,db(a1)
  assert any(x%p for x in a0) and any(x%p for x in a1)
 X,Z=a0
 return Z*pow(X,-1,m)%m
def lifted(shiftplus):
 Hs=[];Is=[];Ys=[]
 for j,t in enumerate((sr2,-sr2)):
  e=(3-t)**2%m
  a=1+t; assert (2*t)**2%m==a*(a*a-e)%m
  n=p*arms[j]['order']
  ix=(pow(6,15,n)*pow(3,N,n)*J)%n
  assert n%p==0
  xv,yv=a_sources[j]
  if j==0:xv+=p*shiftplus
  fy=xv*(xv*xv-e)
  yv+=p*((((fy-yv*yv)//p)*pow(2*yv,-1,p))%p)
  assert yv*yv%m==fy%m
  Hs.append(Kx(a,e,(2*h)%n))
  Is.append(Kx(xv,e,(2*ix)%n))
  Ys.append((xv,yv))
 Jx=fold(Hs,Is,m)
 assert Jx['delta']%p==0 and Jx['Npack']%p==141 and Jx['Q2']%p==q*q%p
 assert [u%p for u in Hs]==hr and [u%p for u in Is]==[s['U']**2%p for s in arms]
 return Jx,Ys
checks=[lifted(i) for i in (0,1)]
assert checks[0][0]['delta']!=checks[1][0]['delta']
witness,pts=next((T,Q) for T,Q in checks if T['delta']!=0)
print(json.dumps(dict(scope='same exact shifted multiplication on variable base, not the actual P0',
 beta=B,p=p,sqrt2_mod_p2=sr2,actual_mod_p=true,specialization_mod_p=var,
 variable_local_input_mod_p2=pts,variable_local_delta_stripped=witness['delta']//p,
 variable_fold_mod_p2=witness,replay_arms=arms),indent=2,sort_keys=True))
