import json
from pathlib import Path
from hashlib import sha256
import sys
def pinned(arg,sha):
 b=Path(arg).read_bytes();assert sha256(b).hexdigest()==sha; return json.loads(b)
p=53
F=pinned(sys.argv[1],'7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a')
T=pinned(sys.argv[2],'ded42d7df018fd526c3a57a61d8d33a92395733a32e086e15aefc4cd989230c6')
d=F['d'];q=p**13
H=tuple(reversed(T['irreducible_degree13_factor_desc']))
N=13
def k(v):return (v%p,)+(0,)*(N-1)
def add(a,b):return tuple((x+y)%p for x,y in zip(a,b))
def scale(a,b):return tuple(x*b%p for x in a)
def mul(a,b):
 c=[0]*(2*N-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 for j in range(2*N-2,N-1,-1):
  for i in range(N):c[i+j-N]-=H[i]*(c[j]%p)
 return tuple(x%p for x in c[:N])
def eval_(fs,x):
 v=k(0)
 for a in fs:v=add(mul(v,x),k(a))
 return v
def pw(v,m):
 t=k(1)
 for b in bin(m)[2:]:
  t=mul(t,t)
  if b=='1':t=mul(t,v)
 return t
def sub(a,b):return add(a,scale(b,-1))
def inv(a):
 assert a!=k(0)
 return pw(a,q-2)
def div(a,b):return mul(a,inv(b))
u=(0,1)+(0,)*(N-2)
assert pw(u,q)==u and pw(u,p)!=u
assert eval_(F['x_root_poly_coefficients'],u)==k(0)
X=scale(u,d)
W=tuple(reversed(T['chosen_W_in_u_basis_desc']))
Y=scale(W,d*pow(169,-1,p))
curve=lambda x:mul(x,mul(sub(x,k(d)),add(x,k(3*d))))
assert mul(Y,Y)==curve(X)
P=(X,Y)
def plus(A,B):
 if A is None:return B
 if B is None:return A
 x,y=A;z,w=B
 if x==z and add(y,w)==k(0):return None
 if x==z:s=div(add(add(scale(mul(x,x),3),scale(x,4*d)),k(-3*d*d)),scale(y,2))
 else:s=div(sub(w,y),sub(z,x))
 U=sub(sub(sub(mul(s,s),k(2*d)),x),z)
 V=sub(mul(s,sub(x,U)),y)
 assert mul(V,V)==curve(U)
 return (U,V)
P2=plus(P,P);P4=plus(P2,P2);P8=plus(P4,P4)
assert plus(plus(P8,P4),P) is None
scores=[0,0,0]
for a in range(1,13):
 B=None
 for j,b in enumerate((P,P2,P4,P8)):
  if a&(1<<j):B=plus(B,b)
 x,y=B; v=scale(x,13*pow(d,-1,p)); w=scale(y,169*pow(d,-1,p))
 proj=pow(12*a,-1,13)
 for i,z in enumerate((v,add(k(1),w),add(k(2),w))):
  assert z!=k(0)
  t=pw(z,(q-1)//13)
  assert t==k(t[0])
  i0=next(j for j in range(13) if pow(T['zeta13_mod53'],j,p)==t[0])
  scores[i]=(scores[i]+proj*i0)%13
assert scores==[0,0,8]
# Euler characters / no reuse of author's y table.
def euler(a):return 0 if a%p==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
n=p+1+sum(euler(x*(x-d)*(x+3*d)) for x in range(p))
assert n==52
print('degree-13 branch, curve cardinality',n,'projected v,1+W,2+W scores',scores)
