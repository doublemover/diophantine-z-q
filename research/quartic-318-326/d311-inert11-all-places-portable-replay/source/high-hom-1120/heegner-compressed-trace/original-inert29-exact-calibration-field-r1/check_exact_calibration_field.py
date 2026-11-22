from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json,math
class Arit:
 def __init__(self,n):
  self.maskn=n;self.N=4*(1<<n)
  self.I=[(0,0),(0,2)]+[(k,j) for j in range(1<<n) for k in range(4) if (k,j) not in ((0,0),(0,2))]
  self.map={a:i for i,a in enumerate(self.I)}
  Q={}
  for a,b in self.I:
   for c,d in self.I:
    u=a+c;v=b^d
    w=math.prod(e for i,e in enumerate((-1,2,3)[:n]) if (b&d)>>i&1)
    Q[self.map[a,b],self.map[c,d]]=tuple((self.map[k,v],w*e) for k,e in ([(u,1)] if u<4 else [(u-4,1),(u-2,-4)] if u<6 else [(2,17),(0,-4)]))
  self.Q=Q
 def c(self,z):return [z]+[0]*(self.N-1)
 def m(self,x,y):
  z=self.c(0)
  for i,a in enumerate(x):
   if not a:continue
   for j,b in enumerate(y):
    if not b:continue
    for k,v in self.Q[i,j]:z[k]+=v*a*b
  return z
 def p(self,x,n):
  z=self.c(1)
  while n:
   if n&1:z=self.m(z,x)
   x=self.m(x,x);n//=2
  return z
 def add(self,*args):return list(map(sum,zip(*args)))
 def u(self,a,x):return [a*y for y in x]
 def ver(self,X,Y,J,J2,H,H2):
  a,m,p,u,c=self.add,self.m,self.p,self.u,self.c
  pol=p(X,8);x4=p(X,4)
  assert p(Y,2)==a(pol,u(14,x4),c(1))
  def data(Xn,Xd,Yn,Yd):
   # Input rational function X=Xn/Xd and Y=Yn/Yd. Here Yd=Xd^4.
   assert Yd==p(Xd,4)
   b=a(Yn,p(Xn,4),Yd)
   ab=a(m(a(Xn,u(-2,Xd)),b),u(6,m(Xn,Yd)))
   bb=m(Xd,b)
   for off in (2,4,16):ab,bb=p(ab,2),m(bb,a(ab,u(off,bb)))
   a0=p(a(ab,u(256,bb)),3);b0=m(bb,p(ab,2))
   assert any(b0)
   return a0,b0
  v,w=data(X,c(1),Y,c(1));assert v==m(w,J)
  Xn=a(X,c(1));Xd=a(X,c(-1));Yn=u(4,Y);Yd=p(Xd,4)
  v,w=data(Xn,Xd,Yn,Yd);assert v==m(w,J2)
  for T,G in [(J,H),(J2,H2)]:
   z=c(0)
   for t in G:z=a(m(z,T),c(t))
   assert not any(z)
class Pad:
 def __init__(self,k):
  self.K=k;self.M=29**k; self.one=(1,0);self.zero=(0,0)
 def c(self,n):return n%self.M,0
 def a(self,x,y):
  M=self.M;return (x[0]+y[0])%M,(x[1]+y[1])%M
 def l(self,x,y):
  M=self.M;return (x[0]-y[0])%M,(x[1]-y[1])%M
 def m(self,x,y):
  M=self.M;return (x[0]*y[0]+2*x[1]*y[1])%M,(x[0]*y[1]+x[1]*y[0])%M
 def p(self,x,n):
  r=self.one
  while n:
   if n&1:r=self.m(r,x)
   x=self.m(x,x);n//=2
  return r
 def d(self,x,y):
  M=self.M;j=pow((y[0]**2-2*y[1]**2)%M,-1,M)
  return self.m(x,(y[0]*j%M,-y[1]*j%M))
 def root(self,H,x):
  a,l,m,d=self.a,self.l,self.m,self.d
  for _ in range(self.K.bit_length()+2):
   f=g=self.zero
   for q in H:g=a(m(g,x),f);f=a(m(f,x),q)
   if f==self.zero:return x
   x=l(x,d(f,g))
  assert False
 def gen(self,V):
  c,m,p=self.c,self.m,self.p
  a=self.root([c(j) for j in [1,0,4,0,-1]],(4,0))
  i=self.root([c(j) for j in [1,0,1]],(12,0))
  z=self.root([c(j) for j in [1,0,-3]],(0,4))
  return [m(p(a,k),m(p(i,j&1),m(p((0,1),j>>1&1),p(z,j>>2&1)))) for k,j in V.I]

def split(t):return t%29,t//29

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
DON=ROOT/'rc-native-helper-20261120/ct-level48-Kminus5-exact-calibration-lifts-r1'
D=json.loads((HERE/'EXACT-CALIBRATION-FIELD.json').read_text())
donjson=DON/'EXACT-KMINUS5-CALIBRATION-LIFTS.json'
assert sha256((DON/'SHA256SUMS').read_bytes()).hexdigest()==D['donor_manifest_sha256']
assert sha256(donjson.read_bytes()).hexdigest()==D['donor_json_sha256']
for row in (DON/'SHA256SUMS').read_text().splitlines():
    h,f=row.split(maxsplit=1)
    assert sha256((DON/f).read_bytes()).hexdigest()==h
L=json.loads(donjson.read_text());Hs=L['exact_order_class_polynomials']
assert D['radical_polynomials']=={'A':[1,0,4,0,-1],'i':[1,0,1],'sqrt2':[1,0,-2],'sqrt3':[1,0,-3]}
assert D['named_reductions_mod29']=={'A':[4,0],'i':[12,0],'sqrt2':[0,1],'sqrt3':[0,4]}

# Replay no reconstruction. Check each supplied rational vector as an exact
# characteristic-zero identity, then evaluate it in the named Witt ring.
slots={16:Arit(2),32:Arit(3)}
P=Pad(6)
basis={d:P.gen(a) for d,a in slots.items()}
def val(x,bb):
    q=P.zero
    for u,v in zip(x,bb):
        c=P.d(P.c(u.numerator),P.c(u.denominator))
        q=P.a(q,P.m(c,v))
    return q

flags=D['exact_flags']
assert len(flags)==len(L['calibration_flags'])==32
assert sorted(f['flag'] for f in flags)==[f['flag'] for f in L['calibration_flags']]
d0=[1]*4;b0=[0]*4
for f,g in zip(flags,L['calibration_flags']):
    assert f['flag']==g['flag']
    assert f['poly_source']==g['source_conductor'] and f['poly_target']==g['target_conductor']
    n=f['dimensions'];R=slots[n]
    assert n==(32 if max(g['source_conductor'],g['target_conductor'])==12 else 16)
    V=[list(map(F,w)) for w in f['exact']]
    for j,v in enumerate(V):
        assert len(v)==n
        d0[j]=math.lcm(d0[j],*(c.denominator for c in v))
        b0[j]=max(b0[j],*(abs(c.numerator).bit_length() for c in v))
    R.ver(*V,Hs[str(f['poly_source'])],Hs[str(f['poly_target'])])
    T=[val(v,basis[n]) for v in V]
    assert T[:2]==[tuple(g['x']),tuple(g['y'])]
    assert [tuple(z%29 for z in t) for t in T]==list(map(split,f['flag']+[g['source_j'],g['target_j']]))
assert d0==D['denominator_lcm'] and b0==D['maximum_numerator_bits']
assert all(q&(q-1)==0 for q in d0)
print('32 full flags; both endpoint CM equations and level identities; exact named 29^6 reductions')
print('maximum numerator bits',b0,'denominator lcm',d0)
