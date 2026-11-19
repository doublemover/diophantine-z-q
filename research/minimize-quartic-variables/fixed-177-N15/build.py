"""Compile the changed chart, collect literal coefficients, and compare frozen artifacts."""
import json,hashlib,math,sys
from itertools import product
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
D=Path(__file__).resolve().parent
C=149**15; K=557*149**67
def mul(p,q):
 s=Counter()
 for i,u in p.items():
  for j,v in q.items():s[tuple(sorted(i+j))]+=u*v
 return Counter({m:k for m,k in s.items() if k})
def comb(*parts):
 s=Counter()
 for a,p in parts:
  for m,v in p.items():s[m]+=a*v
 return Counter({m:k for m,k in s.items() if k})
def lin(v):return {(v,):1}
one={():1};t=comb((149,lin(37)),(-7151,one))
t2=comb((149**2,lin(60)),(-2*149*7151,lin(37)),(7151**2,one))
v=lin(63);w=lin(72);q=comb((-3,one),*( (1,lin(i)) for i in (129,134,176)))
P=[1]
for k in (117504,235008):
 for a,b in ((k,2401),(k,2400),(32*k,77175)):
  v0=[0]*(len(P)+1)
  for j,h in enumerate(P):
   v0[j]+=(b-a)*h;v0[j+1]+=a*h
  P=v0
A=P; lam=F(A[1],2*A[0]);B=A[2]-A[0]*lam**2;E=A[3]-B*lam
raw=(D/'donor178/QUADRICS.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='8f5f9b89fe3211107e31929b2b8934fd704b3d61139bd2f7928b67bcde5f69d0'
source=json.loads(raw);out=[];changes={}
for r in source:
 i=r['id']; base={tuple(m):c for m,c in r['terms']}; pol=dict(base); name=r['name']
 if i==23:continue
 if i in (5,8,10,13,17,20,138,141):
  pol={tuple(x for x in m if x!=71):c*(C if 71 in m else 1) for m,c in base.items()}
 elif i==16:
  pol=comb((1,mul(v,t2)),(-1,one),(-lam,t));name='scalar.doubleInterpolationFirst'
 elif i==22:
  assert pol.pop((70,71))==-C;pol[(70,72)]=-C*C
 elif i in (32,33,38,39):
  pol={tuple(72 if x==71 else x for x in m):c*(C if 71 in m else 1) for m,c in base.items()}
 elif i in (34,35):
  j=i-34
  pol={m:c for m,c in base.items() if 83+j not in m};pol[(72,83+j)]=1
 elif i in (36,37):
  coef=pol.pop((71,178));pol[(72,72)]=coef*C
 elif i in (40,41):
  j=i-40
  assert pol.pop((87+j,178))==C
  pol=comb((1,pol),(C,mul(lin(87+j),q)))
 elif i==136:
  pol=comb((C,mul(w,t2)),(-K*A[0],mul(v,v)),(-K*B,v),(-K*E,mul(t,v)),(-K*(A[4]-E*lam),one),(-K*A[5],t),(-K*A[6],t2));name='scalar.doubleInterpolationSecond'
 if pol!=base:changes[i]=name
 den=math.lcm(*(F(c).denominator for c in pol.values()))
 terms=sorted((tuple(x-(x>71) for x in m),int(c*den)) for m,c in pol.items() if c)
 g=math.gcd(*(c for m,c in terms))
 assert all(71 not in m for m in pol)
 out.append(dict(id=len(out)+1,name=name,terms=[[list(m),c//g] for m,c in terms]))
assert len(out)==149 and all(len(m)<=2 for r in out for m,c in r['terms'])
tot=Counter()
for r in out:
 p={tuple(m):c for m,c in r['terms']};tot.update(mul(p,p))
p={m:v for m,v in sorted(tot.items()) if v}
def spell(m,c):
 S=[f'x{v}'+(f'^{n}' if n!=1 else '') for v,n in sorted(Counter(m).items())]
 if not S or abs(c)!=1:S.insert(0,str(abs(c)))
 return ('-' if c<0 else '+')+'*'.join(S)
s=''.join(spell(m,c) for m,c in p.items()).lstrip('+').encode()
def capsule(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
assert {i for m in p for i in m}==set(range(1,178)) and p[(1,1,1,1)]==1
files={'QUADRICS.json':capsule(out),'POLYNOMIAL.json':capsule(list(p.items())),'quartic177-N15.txt':s,'ROW-MAP.json':capsule(dict(oldRemovedRow=23,oldRemovedSlot=71,changed={str(i):n for i,n in changes.items()},C=C,K=K,coefficients=P,lam=str(lam),B=str(B),D=str(E)))}
for f,bts in files.items():
 if '--emit' in sys.argv:(D/f).write_bytes(bts)
 else:assert (D/f).read_bytes()==bts,f
print('PASS',len(out),len(p),max(abs(c).bit_length() for c in p.values()),len(s),hashlib.sha256(s).hexdigest())
