from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import comb
from itertools import product
import json,sympy as S
import tempfile,shutil
p=Path(__file__).resolve().parent
tmp=tempfile.TemporaryDirectory();tmpdir=Path(tmp.name);a=tmpdir/'donor';b=tmpdir/'pre-normalization';prepared=tmpdir/'prepared168';a.mkdir();b.mkdir();prepared.mkdir()
for n in ['QUADRICS.json','TRANSFER.json']:
 shutil.copyfile(p/('DONOR169-'+n),a/n)
for n in ['QUADRICS.json','TRANSFER.json','QUARTIC.json']:
 shutil.copyfile(p/n,prepared/n)
import hashlib
si=json.loads((p/'SHA256SUMS.json').read_bytes());assert all(hashlib.sha256((p/n).read_bytes()).hexdigest()==d for n,d in si.items())
table=json.loads((prepared/'QUADRICS.json').read_bytes());T0=json.loads((prepared/'TRANSFER.json').read_bytes())
for row0 in table['rows']:
 for term in row0['terms']:term['parameterPower']-=T0['cleared_parameter_powers'][str(row0['id'])]
(b/'QUADRICS.json').write_text(json.dumps(table));(b/'TRANSFER.json').write_text(json.dumps(T0))
def get(p,sub):
 T=json.loads((p/'TRANSFER.json').read_bytes());RR=json.loads((p/'QUADRICS.json').read_bytes())['rows'];ren={v:int(k)for k,v in T['renumber'].items()};w=T['weights'];out=[]
 for r in RR:
  z=Counter()
  for t in r['terms']:
   c=F(t['coefficient']);ex=t['parameterPower'];ids=[ren[i]for i in t['monomial']];e=ids.count(900)-ids.count(901)-sum(w['x%d_0'%i]for i in ids if i not in(900,901));m=tuple(sorted(i for i in ids if i not in(900,901) and not(sub and i==334)));k=ids.count(334) if sub else 0
   for choice in product((0,1,2),repeat=k):
    key=e+choice.count(0),ex,tuple(sorted(m+(314,)*choice.count(1)));z[key]+=c*2**choice.count(2)*(-1)**choice.count(1)
  z={j:f for j,f in z.items()if f}
  if z:
   m=min(z);z={(e-m[0],k,s):f/z[m]for (e,k,s),f in z.items()}
  out.append((r['name'],z))
 return out,RR,T
A,_,_=get(a,False);B,R,t=get(b,True);assert B[:129]==A[:129],[(aa[0],bb[0])for aa,bb in zip(A,B)if aa!=bb][:10];assert len(B)==142 and not B[-1][1] and B[-1][0]=='q.guard'
assert t['renumber']['1']==1 and t['weights']['x1_0']==0 and t['weights']['x314_0']==t['weights']['x334_0']==0
u,q,C=S.symbols('U q C'); xx=lambda i:u if i==314 else q+2-u if i==334 else S.Symbol('X%d'%i)
Z=lambda poly,d:sum(f*q**e*C**k*S.prod(xx(i)for i in xs)for (e,k,xs),f in poly.items()).expand()
marks=sorted((1-F(x))**2 for x in ['0','-1/2','-1','1/2399','-32/407'])
Y=S.symbols('y');Q=S.prod(Y-r for r in marks[:2]);G=S.prod(Y-r for r in marks[2:]);D,L=S.div(G,Q,Y);assert S.degree(D,Y)==1 and S.degree(L,Y)==1 and S.gcd(Q,L)==1
XX=S.symbols('x');nu=XX*Q.subs(Y,XX**2)+L.subs(Y,XX**2);P=(Q*G).subs(Y,XX**2);assert S.gcd(P,nu)==1 and S.degree(nu**2-P,XX)==8 and S.LC(S.Poly(nu**2-P,XX))>0
for j,offset,v,out in [(0,310,2,82),(1,330,86,96)]:
 y,A,z,U,H=[xx(offset+i)for i in [0,1,3,4,8]];x=xx(v)/q-1
 eq=[y-x*x,A-Q.subs(Y,y),z*A-L.subs(Y,y),U*(D.subs(Y,y)+z)-(x+z)**2,U*H-U**2-U*xx(300)-q**2,2045**2*q*xx(out)*U-816**2*H**2]
 for l,(_,p0)in zip(eq,B[129+j*6:135+j*6]):
  rat=S.factor(Z(p0,t)/l);assert rat.as_powers_dict().keys()<=set([q]+[i for i in rat.as_powers_dict() if i.is_Rational]),rat
ex=Counter()
for r in R:
 for i in r['terms']:
  for o in r['terms']:ex[(i['parameterPower']+o['parameterPower'],tuple(sorted(i['monomial']+o['monomial'])))]+=int(i['coefficient'])*int(o['coefficient'])
ex={k:v for k,v in ex.items()if v};print('PASS:',len(R),len(ex),len(set(s for k,s in ex)),max(len(s)for k,s in ex),{k:v for (k,s),v in ex.items()if s==(1,)*4},len(set(v for k,s in ex for v in s)));print('extra finite bad:',S.factorint(abs(S.resultant(P,nu,XX).p)),S.factorint(S.resultant(P,nu,XX).q))
prepared=b.parent/'prepared168';PS=json.loads((prepared/'QUADRICS.json').read_bytes())['rows'];T2=json.loads((prepared/'TRANSFER.json').read_bytes())
assert t['weights']==T2['weights'] and t['renumber']==T2['renumber']
ex=Counter()
for r,rn in zip(R,PS,strict=True):
 k=min(t['parameterPower']for t in r['terms']);assert rn['terms']==[t|{'parameterPower':t['parameterPower']-k}for t in r['terms']];assert rn['id']==r['id'] and rn['name']==r['name']
 for i in rn['terms']:
  for j in rn['terms']:
   ex[i['parameterPower']+j['parameterPower'],tuple(sorted(i['monomial']+j['monomial']))]+=int(i['coefficient'])*int(j['coefficient'])
ex={k:v for k,v in ex.items()if v};assert ex=={(k,tuple(m)):int(v)for k,m,v in json.loads((prepared/'QUARTIC.json').read_bytes())['terms']}
print('prepared',len(ex),len(set(m for k,m in ex)),max(k for k,m in ex),{k:v for (k,s),v in ex.items()if s==(1,)*4})
