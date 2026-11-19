"""Transparent rational expansion, exact torus pullbacks, and rank/order checks. Python stdlib."""
from pathlib import Path
from collections import Counter
from itertools import product
from fractions import Fraction as F
from math import prod,gcd
import json,hashlib
p=Path(__file__).resolve().parent
J=lambda n:json.loads((p/n).read_bytes())
O=J('ORIGINAL-PHYSICAL.json');old=J('PREDECESSOR-168-QUADRICS.json');ot=J('PREDECESSOR-168-TRANSFER.json')
new=J('QUADRICS.json');nt=J('TRANSFER.json')
def clean(d):return {k:v for k,v in d.items()if v}
def norm(d):
 d=clean(d)
 if not d:return {}
 e,b,c,m=min(d);k0=d[e,b,c,m]
 return {(x-e,y-b,z-c,m):v/k0 for (x,y,z,m),v in d.items()}
def harm(d):
 t=Counter()
 for (e,b,c,m),a in d.items():
  k=m.count(334);m=tuple(j for j in m if j!=334)
  for ss in product((0,1,2),repeat=k):
   key=e+ss.count(0),b,c,tuple(sorted(m+(314,)*ss.count(1)))
   t[key]+=a*2**ss.count(2)*(-1)**ss.count(1)
 return clean(t)
def iv(T):return {v:int(k)for k,v in T['renumber'].items()}
def back(r,T,U):
 inv=iv(T);d=Counter();w=T['weights']
 for t in r['terms']:
  ids=[inv[j]for j in t['monomial']];m=tuple(v for v in ids if v not in U)
  e=sum(U.get(j,(0,0))[0]for j in ids)-sum(w[f'x{v}_0']for v in m);b=sum(U.get(j,(0,0))[1]for j in ids)-sum(w.get(f'x{v}_1',0)for v in m)
  d[e,b,t['parameterPower'],tuple(sorted(m))]+=F(t['coefficient'])
 return norm(harm(d))
def oldrow(row):return {(e,0,c,tuple(m)):F(a)for e,c,m,a in row}
for (n,t),r in zip(O,old['rows'][:-1],strict=True):
 assert n==r['name'] and norm(harm(oldrow(t)))==back(r,ot,{901:(-1,0)}),n
assert not back(old['rows'][-1],ot,{901:(-1,0)}) and len(O)==141
def sub(v):
 if v==45:return [(1,1,(),1),(1,0,(),-48)]
 if v==101:return [(0,-1,(),1)]
 if v in (201,202):return [(-1,-1,(17+v-201,),1),(-1,-1,(29+v-201,),-1)]
 if v in (203,204):return [(-1,-1,(150+v-203,),1),(-1,-1,(31+v-203,),-1 if v==203 else 1)]
 return [(0,0,(v,),1)]
D=[];extra=None
for n,t in O:
 if n in ('new.scalar.inverse','cleared.E1','input.cleared'):continue
 y=Counter()
 for (e,b,c,m),a in oldrow(t).items():
  for y0 in product(*(sub(i)for i in m)):
   h=(e+sum(z[0]for z in y0),sum(z[1]for z in y0),c,tuple(sorted(v for z in y0 for v in z[2])));y[h]+=a*prod(z[3]for z in y0)
 y=clean(y)
 if n=='new.aggregate':
  bit={k:v for k,v in y.items()if any(i in k[-1]for i in (209,210))};y={k:v for k,v in y.items()if k not in bit};bit[0,0,0,(605,)]=-1;y[0,0,0,(605,)]=1;extra=('new.firstTrace',bit)
 D.append((n,y))
D.append(extra);U={int(k):tuple(v)for k,v in nt['units'].items()}
for (n,y),r in zip(D,new['rows'][:len(D)],strict=True):
 assert n==r['name'] and norm(harm(y))==back(r,nt,U),n
inv=iv(nt)
def actual(r):return {tuple(inv[i]for i in t['monomial']):int(t['coefficient'])for t in r['terms']}
expectedguards=[{():-1,(314,901):1,(334,901):1,(901,):-2},{():-1,(45,101):1},{(601,):1,(45,314):-1,(45,334):-1,(45,):2},{(602,):1,(45,901):-1}]
assert [actual(r)for r in new['rows'][len(D):]]==expectedguards
assert all(nt['weights'][f'x{i}_{j}']==0 for i in(314,334,1)for j in(0,1))
assert U=={900:(1,0),901:(-1,0),45:(0,1),101:(0,-1),601:(1,1),602:(-1,1)}
assert not {201,202,203,204,900}.intersection(inv.values())
q=Counter()
for r in new['rows']:
 assert all(0<=len(t['monomial'])<=2 and t['parameterPower']>=0 for t in r['terms'])
 assert gcd(*(abs(int(t['coefficient']))for t in r['terms']))==1
 for a,b in product(r['terms'],repeat=2):q[a['parameterPower']+b['parameterPower'],tuple(sorted(a['monomial']+b['monomial']))]+=int(a['coefficient'])*int(b['coefficient'])
q=clean(q);assert q=={(k,tuple(m)):int(c)for k,m,c in J('QUARTIC.json')['terms']}
assert len(new['rows'])==141 and set(i for k,m in q for i in m)==set(range(1,168))
assert len(q)==2828 and len({m for k,m in q})==2821 and q[0,(1,)*4]==1 and len([1 for k,m in q if m==(1,)*4])==1
if (p/'SOURCE-HASHES.json').exists():
 for k,h in J('SOURCE-HASHES.json').items():assert hashlib.sha256((p/k).read_bytes()).hexdigest()==h,k
print('PASS: 142 predecessor rows, 137 symbolic successor rows + 4 guards, 167/141, 2828 terms; pure input coefficient 1.')
