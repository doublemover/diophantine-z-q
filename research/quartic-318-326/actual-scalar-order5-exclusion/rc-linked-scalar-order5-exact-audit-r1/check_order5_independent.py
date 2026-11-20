"""Independent actual order-five calculation, no prime scan, pure stock Python."""
from functools import lru_cache
from math import gcd, prod
import json

R=4376874610839020
B=204618888056724185
M=1+17*144*B
h=473592745039516333133760
z=(0,0);one=(1,0)
def a(u,v): return u[0]+v[0],u[1]+v[1]
def s(u,v): return u[0]-v[0],u[1]-v[1]
def x(u,v): return u[0]*v[0]+2*u[1]*v[1],u[0]*v[1]+u[1]*v[0]
def sc(u,c): return (u[0]*c,u[1]*c)
def conj(u): return u[0],-u[1]
def exact(u,v):
  n=x(v,conj(v))[0]
  return tuple(ediv(t,n) for t in x(u,conj(v)))
def ediv(t,n):
  q,r=divmod(t,n);assert not r;return q
def det(mat):
  a=[r.copy() for r in mat]
  prev=one; sgn=1;n=len(a)
  for k in range(n-1):
    if a[k][k]==z:
      j=next((j for j in range(k+1,n) if a[j][k]!=z),None)
      if j is None:return z
      a[k],a[j]=a[j],a[k];sgn=-sgn
    for i in range(k+1,n):
      for j in range(k+1,n):
        a[i][j]=exact(s(x(a[k][k],a[i][j]),x(a[i][k],a[k][j])),prev)
    prev=a[k][k]
  return sc(a[-1][-1],sgn)

n=12
psi5={12:5,10:-62,8:-105,6:300,4:-125,2:50,0:1}
g=[(psi5.get(i,0)*5**(11-i),0) for i in range(n)]
g.append(one)
def mul(u,v):
  r=[z]*(len(u)+len(v)-1)
  for i,L in enumerate(u):
    for j,T in enumerate(v):r[i+j]=a(r[i+j],x(L,T))
  return r
def reduce(u,monic=g):
  k=len(monic)-1; v=[*u]+[z]*max(0,k-len(u))
  for j in range(len(v)-1,k-1,-1):
    if v[j]!=z:
      for i in range(k):v[j-k+i]=s(v[j-k+i],x(v[j],monic[i]))
  return v[:k]
def cols(p,monic):
  D=len(monic)-1
  return [reduce([z]*j+p,monic) for j in range(D)]
def trans(v): return [list(r) for r in zip(*v)]
qq=g.copy()
quot=[z]*(n-1)
for j in range(n,1,-1):
  quot[j-2]=qq[j]
  qq[j-2]=s(qq[j-2],sc(qq[j],25))
r=qq[0][0];assert qq[1]==z and r==-512*5**11
S=7*R*r*r
v=reduce(mul(mul(quot,quot),[z,(-25,0),z,one]))
e=[x(L,(60,20)) for L in v];e[0]=a(e[0],(S,0))
w=reduce(mul(reduce(mul(e,e)),reduce(mul(e,e))))
A=trans(cols(w,g))
def matmul(A,B):
  C=[[z]*n for _ in range(n)]
  for i,row in enumerate(A):
    for j,u in enumerate(row):
      if u!=z:
        for k,v in enumerate(B[j]):C[i][k]=a(C[i][k],x(u,v))
  return C
T=A
ts=[n]
for j in range(1,n+1):
  ts.append(tuple(map(sum,zip(*(T[k][k] for k in range(n))))))
  if j!=n:T=matmul(T,A)
# Multiplication-matrix traces, not universal power sums of the polynomial g.
descending=[one]
for k in range(1,n+1):
  val=z
  for j in range(1,k+1):val=s(val,x(descending[k-j],ts[j]))
  descending.append(exact(val,(k,0)))
f=descending[::-1]

def elim(K,Q):
  # Evaluate the reversed characteristic polynomial with specialization
  # q/(K*W).  No inverse of W is taken; use a direct convolution in W.
  q=Q*S**8
  coeffs=[sc(conj(t),q**j*K**(n-j)) for j,t in enumerate(f)][::-1]
  pair=det(trans(cols(coeffs,f)));assert pair[1]==0
  single=det(trans(cols([(-q,0),(K*S**4,0)],f)))
  return abs(pair[0]*x(single,conj(single))[0])

def psi_gcd(m):
  def rd(u):return u[0]%m,u[1]%m
  def p(u,v):return rd(x(u,v))
  def b(u,v):return rd(s(u,v))
  def v(c,u):return rd(sc(u,c))
  P=(1,1); y=(0,2); F=(-11,6); ps2=v(2,y)
  invps2=(0,pow(8,-1,m))
  P2=p(P,P);P4=p(P2,P2);P6=p(P4,P2);F2=p(F,F)
  ps3=rd(a(a(sc(P4,3),sc(p(F,P2),6)),sc(F2,-1)))
  ps4=p(v(4,y),rd(a(a(a(P6,sc(p(F,P4),5)),sc(p(F2,P2),-5)),sc(p(F,F2),-1))))
  start=(z,one,ps2,ps3,ps4)
  def sq(u):return p(u,u)
  def cube(u):return p(u,sq(u))
  @lru_cache(None)
  def psi(t):
    if t<5:return start[t]
    k=t//2
    if t%2:return b(p(psi(k+2),cube(psi(k))),p(psi(k-1),cube(psi(k+1))))
    return p(p(psi(k),invps2),b(p(psi(k+2),sq(psi(k-1))),p(psi(k-2),sq(psi(k+1)))))
  G=gcd(m,*psi(5*h));G0=gcd(G,*psi(h))
  return G,G0,G//gcd(G,pow(G0,G.bit_length(),G))

out=[]
for name,K,Q,want in [('H',144*B,M*M,521),('Lprime',7056*B,48*M*M,89**2*199)]:
  D=elim(K,Q)
  fixed=2*3*5*7*R*M*B
  mod=D//gcd(D,pow(fixed,D.bit_length(),D))
  G,G0,rest=psi_gcd(mod)
  assert rest==want
  out.append(dict(name=name,rawBits=D.bit_length(),bits=mod.bit_length(),
                  bothKilled=str(G),bothIdentity=str(G0),nontrivial=str(rest)))
print(json.dumps(out,indent=2),flush=True)
