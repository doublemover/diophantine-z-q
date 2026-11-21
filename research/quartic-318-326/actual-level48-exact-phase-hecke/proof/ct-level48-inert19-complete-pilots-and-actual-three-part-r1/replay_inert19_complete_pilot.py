from itertools import product
from functools import lru_cache
from random import Random
import hashlib,json
from pathlib import Path
p=19
q=p**8
F=list(product(range(p),repeat=2)); z=lambda n:(n%p,0)
def a(x,y):return ((x[0]+y[0])%p,(x[1]+y[1])%p)
def n(x):return ((-x[0])%p,(-x[1])%p)
def s(x,y):return a(x,n(y))
def m(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def pw(x,k):
 v=z(1)
 while k:
  if k&1:v=m(v,x)
  x=m(x,x);k//=2
 return v
def d(x,y):
 assert y!=z(0)
 return m(x,pw(y,359))
tcoef=next(x for x in F if pw(x,8)==z(1) and pw(x,4)!=z(1))
zero=(z(0),)*4;one=(z(1),)+(z(0),)*3
def E(*x):return (tuple(x),)+(z(0),)*3
c=lambda k:E(*z(k))
def base(x):
 assert x[1:]==zero[1:]
 return x[0]
def A(x,y):return tuple(a(u,v) for u,v in zip(x,y))
def N(x):return tuple(n(u) for u in x)
def S(x,y):return A(x,N(y))
def M(x,y):
 v=[z(0)]*7
 for i in range(4):
  if x[i]==z(0):continue
  for j in range(4):
   if y[j]==z(0):continue
   v[i+j]=a(v[i+j],m(x[i],y[j]))
 for j in range(4,7):
  v[j-4]=a(v[j-4],m(tcoef,v[j]))
 return tuple(v[:4])
def P(x,k):
 v=one
 while k:
  if k&1:v=M(v,x)
  x=M(x,x);k//=2
 return v
@lru_cache(20000)
def I(x):
 assert x!=zero
 return P(x,q-2)
def D(x,y):return M(x,I(y))
def sqr(x):return M(x,x)
def sqrt(x):
 if x==zero:return zero
 if P(x,(q-1)//2)!=one:return None
 odd=q-1;e=0
 while odd%2==0:odd//=2;e+=1
 z0=(z(0),z(1),z(0),z(0))
 assert P(z0,(q-1)//2)==N(one)
 v=P(z0,odd);y=P(x,(odd+1)//2);t=P(x,odd)
 while t!=one:
  i=1;t0=sqr(t)
  while t0!=one:i+=1;t0=sqr(t0)
  assert i<e
  h=P(v,2**(e-i-1));v=sqr(h);y=M(y,h);t=M(t,v);e=i
 assert sqr(y)==x
 return y

L0=c(-1);B0=c(5)
def add(P,Q,L=None,a2=zero):
 if L is None:L=L0
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u and A(y,v)==zero:return None
 if x==u:
  h=D(A(A(M(c(3),sqr(x)),M(M(c(2),a2),x)),L),M(c(2),y))
 else:h=D(S(v,y),S(u,x))
 r=S(S(S(sqr(h),a2),x),u)
 return r,S(M(h,S(x,r)),y)
def ng(P):return None if P is None else (P[0],N(P[1]))
def mu(k,P,L=None,a2=zero):
 if L is None:L=L0
 if k<0:return mu(-k,ng(P),L,a2)
 Q=None
 while k:
  if k&1:Q=add(Q,P,L,a2)
  P=add(P,P,L,a2);k//=2
 return Q
def on(P,L=None,B=None,a2=zero):
 if L is None:L=L0
 if B is None:B=B0
 if P is None:return True
 x,y=P
 return sqr(y)==A(A(A(PW(x,3),M(a2,sqr(x))),M(L,x)),B)
PW=P
def velu(L,B,K):
 R,T=L,B
 for x,_ in K:
  h=A(M(c(3),sqr(x)),L)
  v=A(A(M(c(5),PW(x,3)),M(c(3),M(L,x))),M(c(2),B))
  R=S(R,M(c(5),h));T=S(T,M(c(7),v))
 def f(P):
  if P is None or P in K:return None
  x,y=P
  for U in K:
   V=add(P,U,L)
   assert V is not None
   x=A(x,S(V[0],U[0]));y=A(y,S(V[1],U[1]))
  assert on((x,y),R,T)
  return x,y
 return R,T,f

rng=Random(4819)
def basis(l,k):
 b=[];n0=l**k
 for K in range(128):
  x=tuple((rng.randrange(p),rng.randrange(p)) for _ in range(4))
  y=sqrt(A(A(PW(x,3),M(L0,x)),B0))
  if y is None:continue
  U=mu((p**4-1)//n0,(x,y))
  V=mu(n0//l,U)
  if V is None or b and V in [mu(a,mu(n0//l,b[0])) for a in range(l)]:continue
  assert mu(n0,U) is None
  b.append(U)
  if len(b)==2:return b
 raise ValueError("torsion basis not found")
def reps(l,k):
 n0=l**k;A,B=basis(l,k)
 u=[mu(i,A) for i in range(n0)];v=[mu(i,B) for i in range(n0)]
 allT=[add(a0,b0) for a0 in u for b0 in v]
 assert len(set(allT))==n0**2
 seen=set();R=[]
 for T in allT:
  if T in seen or mu(n0//l,T) is None:continue
  seen.update(mu(k0,T) for k0 in range(n0) if k0%l)
  R.append(T)
 return R
def t8(P8,L):
 u0=mu(4,P8,L)[0]
 aa=M(c(3),u0);bb=A(M(c(3),sqr(u0)),L)
 u=S(mu(2,P8,L)[0],u0);v=S(P8[0],u0)
 assert sqr(u)==bb
 k=D(A(v,D(bb,v)),u)
 return base(D(c(32),S(k,c(6))))
def t16(P16,L,B):
 h0=t8(mu(2,P16,L),L)
 R=mu(8,P16,L)
 L2,B2,f=velu(L,B,[R])
 h1=t8(f(P16),L2)
 out=[t for t in F if a(t,z(2))!=z(0) and d(m(t,t),a(t,z(2)))==h0 and m(t,a(t,z(4)))==h1]
 assert len(out)==1
 return out[0]
def pi(P):return None if P is None else tuple(PW(u,p) for u in P)

rr=E(11,3);uu=E(5,13);t=A(M(c(3),sqr(rr)),c(-1))
def eta7(P):
 if P is None or P==(rr,zero):return None
 x,y=P;h=S(x,rr)
 Q=M(PW(uu,2),A(x,D(t,h))),M(PW(uu,3),M(y,S(one,D(t,sqr(h)))))
 assert on(Q)
 return Q
def nu7(P):
 P=mu(7,P)
 return add(P,add(mu(5,eta7(P)),add(mu(5,pi(P)),mu(4,eta7(pi(P))))))
def ii(P):return None if P is None else (N(P[0]),M(E(0,3),P[1]))
K0=[(c(a),E(0,b)) for a,b in ((13,3),(13,16),(14,4),(14,15))]
FIVE=velu(c(-1),zero,K0)[2]
def eta0(P):
 Q=FIVE(P)
 return None if Q is None else (M(c(4),Q[0]),M(c(8),Q[1]))
def om(T, ns, l,maps):
 R=None
 for nn,U in zip(ns,maps[T]):R=add(R,mu(nn%l,U))
 return R
def find(n,ns,G16,G3,maps):
 u=next(t for t in range(0,16,2) if (t*t-t+(1+n)//4)%16==0)
 U=[P for P in G16 if om(P,ns,16,maps)==mu(u,P)]
 V=[P for P in G3 if om(P,ns,3,maps) is None]
 assert len(U)==len(V)==1
 return U[0],V[0]
def label(U,V,chart):
 t=t16(U,L0,B0)
 L1,B1,f=velu(L0,B0,[V,ng(V)])
 u=t16(f(U),L1,B1)
 return chart[t,u]
def phi(X,Y):
 t=s(X,d(z(1),X));w=d(Y,m(X,X))
 x=d(a(a(w,m(t,t)),z(2)),z(2))
 return E(*x),E(*m(t,x))
def eadd(P,Q):return add(P,Q,c(-3),c(-2))
def etm(k,P):return mu(k,P,c(-3),c(-2))
def short(P):return None if P is None else tuple(base(x) for x in P)

if __name__=='__main__':
 p0=Path(__file__).parent
 inputs=("EXACT-INERT19-TWO-SEEDS.json","EXACT-INERT13-19-ORDERED-LOOKUP.json")
 hashes=("e3d96fd505beda59a340dafe1250f7bb1289361a694bdeda38155aaf495641ae",
         "6c941b5ae921d5a38741bf9c1770e1483ac06e021164b03a03c3cc461c9325cc")
 for fl,hh in zip(inputs,hashes):assert hashlib.sha256((p0/fl).read_bytes()).hexdigest()==hh
 assert pw(tcoef,8)==z(1) and pw(tcoef,4)!=z(1)
 assert pow(361,4,32)==1 and pow(361,2,32)!=1
 s0=json.loads((p0/inputs[0]).read_text())["samples"]
 def dec(i):return i%p,i//p
 chart={tuple(map(dec,k)):tuple(map(dec,v)) for k,v in json.loads((p0/inputs[1]).read_text())["19"]}
 assert len(chart)==len(set(chart.values()))==144
 Tminus=(z(-1),z(0))
 for R in chart.values():
  U=phi(*R)
  assert short(etm(6,eadd(U,ng(pi(U)))))==Tminus
 assert 6**2%19==17 and 17%3==2
 samples={n:dict(classes=0,labels=[],raw=None) for n in (47,119)}
 for branch in ('j7','j1728'):
  B0=c(5) if branch=='j7' else zero
  G16=reps(2,4);G3=reps(3,1)
  assert len(G16)==24 and len(G3)==4
  maps={T:(nu7(T),eta7(T),pi(T),eta7(pi(T))) if branch=='j7' else (T,ii(T),eta0(T),ii(eta0(T)))
           for T in G16+G3}
  for n0 in (47,119):
   vals=samples[n0]
   for row in s0[str(n0)][branch]:
    x,z0,w=row
    ns=(x,1-x,z0,w) if branch=='j7' else ((1-z0)//2,(x-w)//2,z0,w)
    T=label(*find(n0,ns,G16,G3,maps),chart)
    vals["labels"].append([branch,T])
    R=phi(*T)
    assert on(R,c(-3),zero,c(-2))
    vals["raw"]=eadd(vals["raw"],R);vals["classes"]+=1
 for n0,v in samples.items():
  Q=v["raw"];anti=eadd(Q,ng(pi(Q)))
  v.update(raw_trace=short(Q),two_anti=short(etm(2,anti)),raw_four=short(etm(4,Q)),raw_two=short(etm(2,Q)))
  del v["raw"]
  assert etm(2,anti)==etm(4,Q)
  if v["classes"]%2==0:assert pi(Q)==ng(Q)
  if n0==119:assert etm(4,Q) is None and etm(2,Q) is not None
  selected=short(etm(2 if n0==119 else 4,Q))
  d0=-n0%p;sig=next(b for b in range(1,p) if 2*b*b%p==d0)
  assert selected[0][1]==selected[1][0]==0
  xy=(d0*selected[0][0]%p,2*d0*sig*selected[1][1]%p)
  assert xy=={47:(1,17),119:(5,0)}[n0]
  x,y=xy
  assert (y*y-x*(x-n0)*(x+3*n0))%p==0
  v["descended"]=xy
 print(json.dumps(dict(scope="complete oriented toy traces at inert nineteen; no original detector",
  seed_tower=tcoef,all_144_six_phases=Tminus,samples=samples),indent=2,sort_keys=True))
