#!/usr/bin/env python3
"""Exact fixed framed T337 over F673^4, using ± kernel abscissae."""
from pathlib import Path
from hashlib import sha256
import json,random,sys,time,os
d=Path(os.environ.get("HELPER673_T17_DIR",str(Path(__file__).resolve().parent.parent/"ct-level48-cm192-helper673-framed-t17-r1")))
raw=(d/'replay_helper673_framed_t17.py').read_bytes()
assert sha256(raw).hexdigest()=='2fd85fd268649770688a677451c18769ae3478915e0c879732f46154bf97ffe0'
blob=(d/'EXACT-HELPER673-FRAMED-T17.json').read_bytes()
assert sha256(blob).hexdigest()=='2745f5eceb36ad4d40b40e113433cf4da673893f107c538260f616c7d03fa4b1'
base=json.loads(blob)
s=raw.decode();s=s[:s.index('# Supersingular j via')].replace('n=32','n=4').replace('M17=p**16-1','M337=p**2-1')
l=s.index('c=pow');r=s.index('def norm',l)
s=s[:l]+'''c=base["field_relation_c"]
assert c==118 and pow(c,16,p)==p-1
assert pow(p,4,128)==1 and pow(p,2,128)!=1
'''+s[r:]
s=s.replace('assert ex(step_t,32)==c','assert ex(step_t,4)==c')
s=s.replace('assert a\n if a<p','assert a\n if a<p').replace('deg=32','deg=4')
a=s.index('def norm(');b=s.index('def ex(',a)
s=s[:a]+'''def norm(a):
 return ((a&mask)%p)+((((a>>24)&mask)%p)<<24)+((((a>>48)&mask)%p)<<48)+((((a>>72)&mask)%p)<<72)
def add(a,b):return norm(a+b)
def sub(a,b):return norm(a+ALLp-b)
def neg(a):return sub(0,a)
def fmul(a,b):
 r=a*b
 return (((r&mask)+118*((r>>96)&mask))%p) + (((((r>>24)&mask)+118*((r>>120)&mask))%p)<<24) + (((((r>>48)&mask)+118*((r>>144)&mask))%p)<<48) + (((((r>>72)&mask)+118*((r>>168)&mask))%p)<<72)
def scl(a,b):return norm((a%p)*b)
'''+s[b:]
exec(s)
assert 673%337==336 and M337%337==0 and M337%(337*337)!=0
def decode(a):
 assert all(i%8==0 for i,j in a)
 return sum(k<<(w*(i//8)) for i,k in a)
class K:
 def __init__(self,j0,pp):
  self.j=decode(j0);self.A,self.B=ab(self.j)
  self.q=[tuple(decode(x) for x in c) for c in pp]
  assert all(curve(t,self.A,self.B) for t in self.q)
  self.d32={v:i for i,v in enumerate(Jgrid(32,fromA(self.q[0]),fromA(self.q[1]),self.A,4))}
  self.d3={v:i for i,v in enumerate(Jgrid(3,fromA(self.q[2]),fromA(self.q[3]),self.A,4))}
mods=[K(j0,pp) for j0,pp in zip(base['j'],base['order32_and_3_bases'])]
idx={m.j:j for j,m in enumerate(mods)}
def coef(pts,m):
 ret=[]
 for t,P in enumerate(pts):
  g=32 if t<2 else 3
  k=(m.d32 if t<2 else m.d3)[P]
  ret.append(list(divmod(k,g)))
 return ret
RNG=random.Random(673337)
def random_pt(m):
 while True:
  x=RNG.getrandbits(128) # decoded fresh independent residues, no arithmetic carry
  x=sum((x>>(32*i)) % p <<(w*i) for i in range(n))
  y=sqroot(add(fmul(x,add(sq(x),m.A)),m.B),4)
  if y is not None:return x,y,1
def basis(m):
 acc=[]
 for _ in range(120):
  P=JP(M337//337,random_pt(m),m.A)
  if P is None:continue
  assert JP(337,P,m.A) is None
  if not acc:
   acc.append(P)
   arc=[None]
   for _ in range(1,337):arc.append(JA(arc[-1],P,m.A))
   arc=toA(arc,4);continue
  if toA([P],4)[0] not in arc:return acc[0],P
 raise ValueError("entropy")
def kxlines(m):
 P,S=basis(m)
 U=[None];V=[None]
 for _ in range(1,337):
  U.append(JA(U[-1],P,m.A));V.append(JA(V[-1],S,m.A))
 assert JA(U[-1],P,m.A) is None and JA(V[-1],S,m.A) is None
 z=[JA(U[k],V[(k*i)%337],m.A) for i in range(337) for k in range(1,169)]
 z.extend(V[1:169])
 zi=batch_inv([P[2] for P in z],4)
 xs=[fmul(t,sq(i)) for (t,y,x),i in zip(z,zi)]
 assert len(xs)==(337**2-1)//2 and len(set(xs))==len(xs) and all(small(u,2) for u in xs)
 return [xs[i:i+168] for i in range(0,len(xs),168)]
def velu(m,r):
 pA=pB=0
 data=[]
 for x in r:
  xx=sq(x);g1=add(scl(3,xx),m.A);g0=add(fmul(x,add(xx,m.A)),m.B)
  pA=add(pA,g1)
  pB=add(pB,add(scl(5,fmul(x,xx)),add(scl(3,fmul(m.A,x)),scl(2,m.B))))
  data.append((x,scl(2,g1),scl(4,g0)))
 a=sub(m.A,scl(10,pA));b=sub(m.B,scl(14,pB))
 assert small(a,2) and small(b,2)
 den=iter(batch_inv([sub(xx,z) for xx,yy in m.q for z,_,_ in data],4))
 out=[]
 for x,y in m.q:
  x0=x;diff=1
  for z,g1,g0 in data:
   u=next(den);v=fmul(g0,u);r=add(g1,v)
   x0=add(x0,fmul(r,u))
   diff=sub(diff,fmul(add(r,v),sq(u)))
  y0=fmul(y,diff)
  assert curve((x0,y0),a,b)
  out.append((x0,y0))
 return a,b,out
st=time.time()
def calc(i):
 global RNG
 RNG=random.Random(673337+i*17)
 m=mods[i];rows=[]
 for K0 in kxlines(m):
  A,B,im=velu(m,K0)
  j=cal_j(A,B); d=idx[j];m1=mods[d]
  a,b=div(A,m1.A,2),div(B,m1.B,2);u2=div(b,a,2);u=sqroot(u2,4)
  assert u and sq(u2)==a and fmul(sq(u2),u2)==b
  q=[(div(x,u2,4),div(y,fmul(u,u2),4)) for x,y in im]
  assert all(curve(t,m1.A,m1.B) for t in q)
  M=coef(q,m1)
  assert (M[0][0]*M[1][1]-M[0][1]*M[1][0])%2
  assert (M[2][0]*M[3][1]-M[2][1]*M[3][0])%3
  rows.append([d,M])
 assert len(rows)==338
 if '--progress' in sys.argv:print('done',i,time.time()-st,file=sys.stderr)
 return rows
if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 import multiprocessing
 jobs=int(os.environ.get("REPLAY_JOBS","4"))
 inds=[int(x) for x in sys.argv[1:] if x.isdigit()] or list(range(len(mods)))
 if jobs!=1:
  with ProcessPoolExecutor(max_workers=jobs,mp_context=multiprocessing.get_context("fork")) as pool:
   out=dict(zip(inds,pool.map(calc,inds)))
 else:out={i:calc(i) for i in inds}
 if len(out)==56:
  rs=raw.decode()
  exec(rs[rs.index('def pmul('):rs.index('for j,(a,mat0)')])
  edges=[out[i] for i in range(56)]
  FROB=base['FrobI']
  v=rs[rs.index('def mprod('):rs.index('out=dict(')].replace('diag17','diag337').replace('[[17,0],[0,17],[2,0],[0,2]]','[[17,0],[0,17],[1,0],[0,1]]')
  exec(v)
 print(json.dumps(dict(p=673,reference=337,T337=out,checked_dual_edges=56*338 if len(out)==56 else 0,
                      checked_frobenius_commutation_rows=56 if len(out)==56 else 0,
                      scope="exact numerical reference operator, no selected product"),
                  sort_keys=True,separators=(',',':')))
