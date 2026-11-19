from pathlib import Path
import json,itertools,math,os,sys
from fractions import Fraction as F
from collections import Counter
P=Path(__file__).resolve().parent; BASE=P.parents[1]; DONOR=P
source=json.loads((DONOR/'ORIGINAL-PHYSICAL.json').read_text());D={};names=[]
def part(x):
 if x==45:return [(1,1,(),F(1)),(1,0,(),F(-48))]
 assert x!=101
 if x in (201,202):
  of=x-201;return [(-1,-1,(17+of,),1),(-1,-1,(29+of,),-1)]
 if x in (203,204):
  of=x-203;return [(-1,-1,(150+of,),1),(-1,-1,(31+of,),1 if of else -1)]
 return [(0,0,(x,),1)]
def new(name,r):
 D[len(names)+1]={k:v for k,v in r.items() if v};names.append(name)
for name,r in source:
 if name in ('input.cleared','new.scalar.denominator','new.scalar.inverse','cleared.E1'):continue
 tmp=Counter()
 for e,c,m,a in r:
  for f in itertools.product(*(part(x)for x in m)):
   tmp[(e+sum(x[0]for x in f),sum(x[1]for x in f)),c,tuple(sorted(i for x in f for i in x[2]))]+=F(a)*math.prod(x[3]for x in f)
 new(name,tmp)
# beta=2449-51 z, P=beta(beta-2401)(32beta+343).
poly=[1]
for a,b in [(2449,-51),(48,-51),(32*2449+343,-1632)]:
 poly=[(x*a+y*b)for x,y in zip(poly+[0],[0]+poly)]
new('unsaturated.scalar',{((-1,0),0,(113,)):576*149}|{((0,i),1,()):v for i,v in enumerate(poly)})
if True:
 i=names.index('new.aggregate')+1;r=D[i]
 left={k:v for k,v in r.items()if set(k[2]) & {209,210}};right={k:v for k,v in r.items() if k not in left}
 dummy=((0,0),0,(605,));left[dummy]=-1;right[dummy]=1;D[i]=right;new('new.firstTrace',left)
units=[(1,0),(-1,0),(0,1),(0,2)]
unit=dict(zip([900,901,45,101,601,602,603],units));assert len(unit)==len(units)
w=json.loads((P/'WEIGHTS.json').read_text());order=json.loads((P/'ORDER.json').read_text())
marks={'E':[31,35,39,43,50,29],'L':[64,19,239,23,237,54],'R':[205,207,217,219]}
assert all(sorted(x[1] for x in order if x[0]==g)==list(range(len(ids))) for g,ids in marks.items())
assert all(sorted(x[2] for x in order if x[0]==g)==list(range(len(ids))) for g,ids in marks.items())
raw={v:(g,i)for g,ids in marks.items()for i,id0 in enumerate(ids)for v in (id0,id0+1)}
fac=[i for i,n in enumerate(names,1)if n.startswith('rebuilt.factor.')]
assert len(fac)==16
fresh={i:Counter()for i in fac}
# Pure permutation of the incoming signed marks, preserving conjugation and the scalar C.
slot={ (g,i):(j,tuple(ep))for g,i,j,ep in order}
for j,idrow in enumerate(fac):
 for (e,c,m),a in D[idrow].items():
  if not m or m[0] not in raw:fresh[idrow][e,c,m]+=a;continue
  g,i=raw[m[0]]; assert all(raw[v]==(g,i)for v in m)
  n,ep=slot[g,i]
  if g=='E':assert ep==(-1,0)
  if g=='L':assert ep==e
  if g=='R':assert ep==((1 if n%2==0 else 3),0)
  dest=2*(n if g!='R' else 6+n//2)+j%2
  fresh[fac[dest]][ep,c,m]+=a
D.update(fresh)
def word(t):return tuple(sum(unit.get(v,(0,0))[j]for v in t)for j in (0,1))
opts={}
for k in (0,1,2):
 wt={}
 for nw in range(k+1):
  for seq in itertools.combinations_with_replacement(unit,nw):wt.setdefault(word(seq),seq)
 opts[k]=wt
rows=[]
def push(name,r):
 den=math.lcm(*(F(v).denominator for v in r.values()));g=math.gcd(*(int(v*den)for v in r.values()if v));s={k:int(v*den)//g for k,v in r.items()if v};rows.append((name,s))
assert all(w[f'x{a}_{j}']==0 for a in (1,314,334) for j in (0,1))
for i,r in D.items():
 d=Counter()
 for (e,c,m),a in r.items():
  h=tuple(e[j]+sum(w[f'x{x}_{j}']for x in m)-w[f'r{i}_{j}'] for j in (0,1)); ud=opts[2-len(m)][h];d[c,tuple(sorted(m+ud))]+=a
 push(names[i-1],d)
push('harmonic.guard',{(0,(900,901)):1,(0,()):-1})
push('zSquared',{(0,(45,45)):1,(0,(101,)):-1})
out=[]
for i,(n,r)in enumerate(rows,1):
 d=Counter()
 for (c,m),a in r.items():
  pre=tuple(v for v in m if v!=900)
  for qslots in itertools.product(((314,),(334,),()),repeat=m.count(900)):
   d[c,tuple(sorted(pre+sum(qslots,())))]+=a*(-2)**qslots.count(())
 lo=min(e for(e,m),v in d.items()if v)
 out.append(dict(name=n,id=i,shift=-lo,terms=[dict(parameterPower=e-lo,coefficient=str(v),monomial=m)for(e,m),v in sorted(d.items())if v]))
ids=sorted({v for r in out for t in r['terms']for v in t['monomial']});nm={v:i for i,v in enumerate(ids,1)}
assert len(ids)==165 and nm[1]==1
summ=Counter()
for r in out:
 for t in r['terms']:t['monomial']=[nm[v]for v in t['monomial']]
 for a,b in itertools.product(r['terms'],repeat=2):summ[a['parameterPower']+b['parameterPower'],tuple(sorted(a['monomial']+b['monomial']))]+=int(a['coefficient'])*int(b['coefficient'])
poly=[[e,m,str(a)]for(e,m),a in sorted(summ.items())if a];assert max(len(m)for e,m,a in poly)==4;assert [a for e,m,a in poly if m==(1,)*4]==['1']
def outp(n,obj):
 b=(json.dumps(obj,separators=(',',':'),sort_keys=True)+'\n').encode();f=P/n
 if '--emit' in sys.argv:f.write_bytes(b)
 else:assert f.read_bytes()==b,n
outp('QUADRICS.json',dict(variables=len(ids),input=1,rows=out));outp('QUARTIC.json',dict(variables=len(ids),input=1,parameter='C=149^N',terms=poly));outp('RENUMBER.json',nm)
print(len(ids),len(out),len(poly),len({m for e,m,a in poly}))
