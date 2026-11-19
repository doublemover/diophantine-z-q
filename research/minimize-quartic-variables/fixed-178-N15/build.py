"""Rebuild the new weighted-first-point quartic from the exact compact-180 quadrics. No packages."""
import sys,json,hashlib,math
from pathlib import Path
from collections import Counter
from itertools import combinations_with_replacement
D=Path(__file__).resolve().parent
def dumps(o):return (json.dumps(o,separators=(',',':'),sort_keys=True)+'\n').encode()
def digest(b):return hashlib.sha256(b).hexdigest()
def load(name):return json.loads((D/name).read_bytes())
emit='--emit' in sys.argv
base=(D/'donor/QUADRICS.json').read_bytes()
assert digest(base)=='df3ecc34963e714f393a744a47bf4483c265da9ea228aaed8c7f74c3bdf59c79'
rows=json.loads(base);assert len(rows)==152 and all(r['id']==i+1 for i,r in enumerate(rows))
out=[];ids=[i for i in range(1,181)if i not in (164,165)];ren={s:i for i,s in enumerate(ids,1)}
def rule(a,b,v):
 R=rows[a-1];F=rows[b-1]
 assert [(m,c)for m,c in R['terms']if v in m]==[([v],1)] and [(m,c)for m,c in F['terms']if v in m]==[([60,v],-1)]
 raw=Counter()
 for r in (R,F):
  for m,c in r['terms']:
   if v not in m:raw[tuple(m)]+=c
 return [[list(m),c]for m,c in sorted(raw.items())if c]
for k,r in enumerate(rows,1):
 if k in (137,139):continue
 n=r['name'];raw=r['terms']
 if k==78:n='weightedFirst.realAggregate';raw=rule(78,137,164)
 if k==138:n='weightedFirst.imagAggregate';raw=rule(138,139,165)
 ts=[[[ren[i]for i in m],c]for m,c in raw]; assert all(len(m)<=2 for m,c in ts) and math.gcd(*(c for m,c in ts))==1
 out.append(dict(id=len(out)+1,name=n,terms=ts))
sums=Counter()
for r in out:
 for (m,c),(n,d)in combinations_with_replacement(r['terms'],2):sums[tuple(sorted(m+n))]+=c*d*(1 if m==n else 2)
p=[(m,c)for m,c in sorted(sums.items())if c]
assert {j for m,c in p for j in m}==set(range(1,179)) and dict(p)[(1,1,1,1)]==1 and len(out)==150
txt=[]
for m,c in p:
 a=[f'x{i}'+(f'^{e}' if e>1 else '')for i,e in sorted(Counter(m).items())]
 if not a or abs(c)!=1:a.insert(0,str(abs(c)))
 txt.append(('-'if c<0 else '+')+'*'.join(a))
s=''.join(txt).lstrip('+').encode('ascii')
files={'QUADRICS.json':dumps(out),'POLYNOMIAL.json':dumps(p),'quartic178-N15.txt':s,'ROW-MAP.json':dumps({'new_index':ren,'removed':[164,165],'changed':[[78,137],[138,139]],'N':15,'weight':'(X^2+48)^2'})}
for n,b in files.items():
 if emit:(D/n).write_bytes(b)
 else:assert (D/n).read_bytes()==b,n
print('PASS',len(ren),len(out),len(p),max(abs(c).bit_length()for m,c in p),len(s),digest(s))
