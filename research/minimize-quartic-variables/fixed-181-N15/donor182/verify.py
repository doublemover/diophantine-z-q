from pathlib import Path
import sympy as S,json,itertools,hashlib
from fractions import Fraction as F
from collections import Counter
ld=lambda p:json.loads(p.read_bytes())
dn=Path(__file__).resolve().parent
src=dn
si=ld(dn/'SHA256SUMS.json');assert all(hashlib.sha256((dn/k).read_bytes()).hexdigest()==s for k,s in si.items())
def read(d,sub):
 tab=ld(d/('TRANSFER.json' if sub else 'DONOR183-TRANSFER.json'));ret=[];ren={v:int(k)for k,v in tab['renumber'].items()};diag=tab['diagonal149'];wt=tab['weights'];assert ren[1]==1 and wt['x1_0']==0 and not diag['1']
 for r in ld(d/('QUADRICS.json' if sub else 'DONOR183-QUADRICS.json')):
  Z=Counter()
  for m,z in r['terms']:
   a=F(z)*F(149)**-sum(diag[str(i)]for i in m);m=[ren[i]for i in m];t=m.count(900)-m.count(901)-sum(wt['x%d_0'%i]for i in m if i not in (900,901));v=tuple(i for i in m if i not in (900,901) and not(sub and i==317))
   for sel in itertools.product(range(4),repeat=(m.count(317)if sub else 0)):
    n,m1,m2,c=[sel.count(i)for i in range(4)];Z[t+n,tuple(sorted(v+(305,)*m1+(311,)*m2))]+=a*(-1)**(m1+m2)*3**c
  Z={k:v for k,v in Z.items()if v};M=min(Z)if Z else (0,0);ret.append((r['name'],{(e-M[0],v):a/Z[M]for(e,v),a in Z.items()}))
 return ret
base=[(n,p)for n,p in read(src,False)if n!='guard.0'and not n.startswith(('d0.','d1.','d2.'))];O=read(dn,True);assert len(base)==135 and O[:135]==base and O[-1]==('q.guard',{})
q,u,v=S.symbols('q u v');X=lambda i: u if i==305 else v if i==311 else q+3-u-v if i==317 else S.Symbol('x%d'%i)
T=F(3,22);marks=sorted((T-F(a))**2 for a in ['0','-1/2','-1','1/2399','-32/407']);y,x=S.symbols('y x');Q=S.prod(y-z for z in marks[:2]);G=S.prod(y-z for z in marks[2:]);D,L=S.div(G,Q,y);r,s=F(-3,22),F(7175,52778);c=1/(r+s);A=c*(D.subs(y,0)-r*s);assert c==-2399 and A>0;den=(Q*G).subs(y,x*x);num=((x+A)*Q+c*L).subs(y,x*x)
res=S.resultant(den,num,x);gamma={2,3,5,7,11,13,17,37,41,2399,79,89,647,3593};assert res and set(S.factorint(abs(res.p)))|set(S.factorint(res.q))<=gamma;assert S.degree(num**2-den,x)==9 and S.LC(S.Poly(num**2-den,x))>0
for off,ind,pole,start in ((301,2,82,135),(307,86,96,141),(313,410,420,147)):
 y0,Q0,z,U,H=map(X,(off,off+1,off+3,off+4,off+5));xx=X(ind)/q-T
 want=[y0-xx**2,Q0-Q.subs(y,y0),Q0*z-L.subs(y,y0),U*(D.subs(y,y0)+z)-(xx+A+c*z)**2,U*H-U**2-X(300)*U-q*q,2045**2*q*X(pole)*U-816**2*H**2]
 for f,(_,p)in zip(want,O[start:start+6],strict=True):
  g=sum(a*q**e*S.prod(X(i)for i in m)for(e,m),a in p.items());w=S.factor(g/f)
  assert all(i.is_Rational or i==q for i in w.as_powers_dict()),w
Q=Counter()
for row in ld(dn/'QUADRICS.json'):
 for((m,a),(n,b))in itertools.product(row['terms'],repeat=2):Q[tuple(sorted(m+n))]+=a*b
Q={m:c for m,c in sorted(Q.items())if c};assert Q=={tuple(m):z for m,z in ld(dn/'POLYNOMIAL.json')};assert {j for m in Q for j in m}==set(range(1,183)) and Q[(1,)*4]==1
raw=''
for m,c in Q.items():
 t='*'.join('x%d'%i+(('^%d'%k)if k>1 else '')for i,k in sorted(Counter(m).items()));raw+=('-'if c<0 else '+'if raw else '')+(str(abs(c))+('*'if t else '')if abs(c)!=1 or not t else '')+t
assert raw.encode()==(dn/'quartic182-N15.txt').read_bytes();print(len(O),len(Q),len(raw),hashlib.sha256(raw.encode()).hexdigest(),max(abs(z).bit_length()for z in Q.values()))

assert len(O)==154 and len(Q)==3287 and len(raw)==74895 and hashlib.sha256(raw.encode()).hexdigest()=='773ca292f53ac13ec52484c8e6f2ee4cfc9b5bc216a84e80efbb0afd6d09d261' and max(abs(z).bit_length()for z in Q.values())==293
