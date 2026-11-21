#!/usr/bin/env python3
"""Independent affine-formal split-q replay of the exact original a=0 rows."""
import hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parent.parent.parent/'joined-work-20261120'
def read(path,digest):
 b=(D/path).read_bytes()
 assert hashlib.sha256(b).hexdigest()==digest
 return json.loads(b)
S=read('rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json','5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7')
P=read('linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json','d6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c')
W=read('linear-q-literal-order-only-canary-r2/EXACT-ORDER-ONLY-Q.json','0f7167957a8e10351b0a0cba431ceed48557b84533c5fef7e25261b69f413254')
q=3162001;m=q*q
h=int(W['h']);T=int(W['crt_period'])
assert 0<h<T and h%q==2 and T==math.lcm(int(P['preserved_old_modulus']),789968,791033,q)
assert (h-int(S['h']))%int(P['preserved_old_modulus'])==0 and h%789968==0 and h%791033==1
s=1+6**15*3**65536*int(S['J'])
k=2*(s-2)
def luc(n):
 a,b=0,1;r=s%n
 for v in bin(k)[2:]:
  c,d=a*(2*b-r*a)%n,(b*b-a*a)%n
  a,b=(c,d) if v=='0' else (d,(r*d-c)%n)
 return [3723%n,s%n,b,a*pow(s-2,-1,n)%n]
def orbit(rho2):
 D=(3-rho2)**2%m
 R=(False,(1+rho2)%m,2*rho2%m)
 def translation(P,z):
  _,x,y=P
  return False,(x+2*y*z)%m,(y+(3*x*x-D)*z)%m
 def add(P,Q):
  a,x,y=P;b,X,Y=Q
  if a:return (True,(x+X)%m,0) if b else translation(Q,x)
  if b:return translation(P,X)
  dx=(X-x)%m;dy=(Y-y)%m
  if dx%q!=0: l=dy*pow(dx,-1,m)%m
  elif (Y+y)%q!=0:l=(X*X+X*x+x*x-D)*pow(Y+y,-1,m)%m
  elif dy%q!=0:return True,dx*pow(dy,-1,m)%m,0
  else:
   assert P==Q and y%q==0
   return True,2*y*pow(3*x*x-D,-1,m)%m,0
  xx=(l*l-x-X)%m;yy=(l*(x-xx)-y)%m
  assert (yy*yy-xx*(xx*xx-D))%m==0
  return False,xx,yy
 def point(N):
  X=(True,0,0)
  for v in bin(N)[2:]:
   X=add(X,X)
   if v=='1':X=add(X,R)
  return X
 def uv(N):
  a,x,y=point(N)
  assert not a
  I=pow(x*x+D,-1,q)
  return [2*y*I%q,(x**4-6*D*x*x+D**2)*I*I%q]
 return D,point,uv
G=[]
for i,(row,A) in enumerate(zip(P['arms'],W['arms'])):
 n=A['exact_halfpoint_order']
 q2=row['root_mod_p2']; assert q2*q2%m==2
 D,pnt,uv=orbit(q2)
 assert pnt(n)[0] and math.prod(row['order_factors'])==n
 for l in row['order_factors']:
  assert all(l%i for i in range(2,math.isqrt(l)+1)) and not pnt(n//l)[0]
 hloc=h-1 if i==0 else h
 z=pnt(hloc%(n*q))
 assert z[0] and z[1]%q==0 and z[1]!=0 and z[1]==A['formal_z_mod_q2']
 L=luc(n)
 assert L==A['labels_mod_half_order']
 C=[uv(k) for k in L];B=uv(1)
 assert C==A['n_label_UV'] and B==A['base_UV']
 t=D*B[0]**4%q
 pg=(1-61*t*pow(65,-1,q)+16*t*t*pow(195,-1,q))%q
 qg=(1-7*t*pow(13,-1,q))%q
 qj=[(1+5*(p[1]-1)*pow(13,-1,q))%q for p in C[1:]]
 assert [pg,qg,qj]==[A['PG'],A['QG'],A['QJ_nonfirst']]
 G.append(math.prod(-pow(x[0],-1,q) for x in C)%q)
 assert G[-1]==A['root_product']
rho=(G[0]+G[1])*pow(2,-1,q)%q
nm=G[0]*G[1]%q
out=[1,(rho+nm)%q,nm]
assert out==W['scales_mod_q']
assert [pow(4*x**12,-1,q) for x in out]==W['b_over_q_mod_q']
print('Independent lifted formal/modular replay PASS',out,W['b_over_q_mod_q'])
