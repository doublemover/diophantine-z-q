"""Exact, stdlib-only symbolic and fixed-integer verification: --emit creates local tables."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from itertools import product,combinations_with_replacement
from math import prod,lcm,gcd
from functools import reduce
import json,sys,hashlib
P=Path(__file__).resolve().parent
read=lambda d,f:json.loads((P/d/f).read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
D165=P/'donor165'; S=P/'donor182'
# Bind exact substantive, pre-parameter tables, not a guessed donor or new optimization run.
pin=json.loads((P/'PINS.json').read_text());assert all(sha(P/f)==v for f,v in pin.items())
rows=read('donor165','ORIGINAL-PHYSICAL.json');ww=read('donor165','WEIGHTS.json');order=read('donor165','ORDER.json')
tr=read('donor182','TRANSFER.json')
def output(f,x):
 data=(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
 if '--emit' in sys.argv:(P/f).write_bytes(data)
 else:assert (P/f).read_bytes()==data,f
def norm(terms):
 r=Counter()
 for e,c,m,a in terms:r[tuple(e),c,tuple(sorted(m))]+=F(a)
 return {k:a for k,a in r.items()if a}
def pieces(i):
 if i==45:return [(1,1,(),1),(1,0,(),-48)]
 assert i!=101
 if i in [201,202]:
  l=i-201;return [(-1,-1,(17+l,),1),(-1,-1,(29+l,),-1)]
 if i in [203,204]:
  l=i-203;return [(-1,-1,(150+l,),1),(-1,-1,(31+l,),1 if l else -1)]
 return [(0,0,(i,),1)]
def sub(row):
 return norm(((e+sum(a[0]for a in u),sum(a[1]for a in u)),c,sum((z[2] for z in u),()),F(v)*prod(z[3]for z in u))
  for e,c,m,v in row for u in product(*(pieces(i) for i in m)))
old=[(n,sub(r)) for n,r in rows if n not in ('input.cleared','new.scalar.denominator','new.scalar.inverse','cleared.E1')]
poly=[1]
for a,b in [(2449,-51),(48,-51),(32*2449+343,-1632)]:poly=[v*a+w*b for v,w in zip(poly+[0],[0]+poly)]
old += [('unsaturated.scalar',{((-1,0),0,(113,)):576*149}|{((0,i),1,()):a for i,a in enumerate(poly)})]
def split(row,aux):
 L={k:v for k,v in row.items() if set(k[2])&{209,210}};R={k:v for k,v in row.items() if k not in L}
 assert L and R;return R|{((0,0),0,(aux,)):1},L|{((0,0),0,(aux,)):-1}
i=next(i for i,(n,r) in enumerate(old) if n=='new.aggregate')
r,l=split(old[i][1],605);old[i]=(old[i][0],r);old.append(('new.firstTrace',l))
fac=[i for i,(n,r) in enumerate(old) if n.startswith('rebuilt.factor.')];assert len(fac)==16
marks={'E':[31,35,39,43,50,29],'L':[64,19,239,23,237,54],'R':[205,207,217,219]}
raw={k:(g,j) for g,idx in marks.items()for j,i in enumerate(idx)for k in (i,i+1)}
slot={(g,i):(j,tuple(ep)) for g,i,j,ep in order};fresh=[Counter() for i in fac]
for j,ii in enumerate(fac):
 for (e,c,m),a in old[ii][1].items():
  if not m or m[0] not in raw:fresh[j][e,c,m]+=a;continue
  g,i=raw[m[0]];assert all(raw[k]==(g,i)for k in m);j2,e2=slot[g,i]
  assert e2==({'E':(-1,0),'L':e,'R':(1 if not j2%2 else 3,0)}[g])
  jj=2*(j2 if g!='R'else 6+j2//2)+j%2;fresh[jj][e2,c,m]+=a
for i,r in zip(fac,fresh):old[i]=(old[i][0],r)
occ=Counter();uniq=[]
for n,r in old:
 occ[n]+=1;uniq.append((n if occ[n]==1 else n+"#"+str(occ[n]),r))
old=uniq
def weight(x,k):return tuple(ww[x+str(k)+'_'+str(j)] for j in (0,1))
xw={v:weight('x',v) for n,r in old for e,c,m in r for v in m}
rw={n:weight('r',i) for i,(n,r) in enumerate(old,1)};base=dict(old);assert len(base)==len(old)
# Real first aggregate: 14q -> 26q. Imaginary aggregate: 2t0-4t1+2t2-8+S1=0.
fixed={n:r.copy()for n,r in old}
fixed['new.aggregate'][((1,0),0,())]=26
S1=[[0,0,[193],1]]
for i in (201,213,225):
 for j in (i,i+2,i+8):
  S1.extend([[1,0,[i+8,j+1],1],[1,0,[i+9,j],1]])
im,im1=split(sub([[0,0,[2],2],[0,0,[86],-4],[0,0,[700],2],[1,0,[],-8]]+S1),606)
fixed.update({'v62.aggregate.imag':im,'v62.firstImag':im1})
rw['v62.aggregate.imag']=rw['new.aggregate'];rw['v62.firstImag']=rw['new.firstTrace']
xw[700]=xw[2];xw[606]=xw[605]
# Actual new pole suffix; unique private variables, reuse the same scalar norm 112.
mp={96:701,7:702,8:703,9:704,10:705,97:706,98:707,99:708}
for n,r in old:
 if not n.startswith('detector1.'):continue
 nn=n.replace('detector1.','detector2.');fixed[nn]=norm((e,c,[mp.get(i,i)for i in m],v)for (e,c,m),v in r.items());rw[nn]=rw[n]
assert sum(n.startswith('detector2.')for n in fixed)==5
for x,y in mp.items():xw[y]=xw[x]
# Independent arithmetic determination of the three exact Γ-safe contact charts.
mid=F(3,22);marks0=list(map(F,['0','-1/2','-1','1/2399','-32/407']))
roots=sorted((x-mid)**2 for x in marks0)
def coeff(rr):
 a=[F(1)]
 for z in rr:a=[t-z*u for t,u in zip([0]+a,a+[0])]
 return a
q0,q1,_=coeff(roots[:2]);g0,g1,g2,_=coeff(roots[2:]);d=g2-q1;l0=g0-d*q0;l1=g1-q0-d*q1
r,s=F(-3,22),F(7175,52778);assert sorted([r*r,s*s])==roots[:2]
c=1/(r+s);A=c*(d-r*s);a=A-mid;assert A>0
assert [str(x)for x in(q0,q1,F(1))]==tr['qcoeff'] and str(c)==tr['c'] and str(A)==tr['A'] and str(d)==tr['d'] and list(map(str,[l0,l1]))==tr['L']
good={2,3,5,7,11,13,17,37,41,2399,79,89,647,3593}
def unit(x):
 z=abs(x.numerator*x.denominator);assert z
 for p in good:
  while z%p==0:z//=p
 return z==1
for b in marks0:
 for t in (mid-b,b-mid):
  y=t*t;Q=y*y+q1*y+q0;assert unit((t+A)*Q+c*(l0+l1*y))
for j,(T,B,y,Q,z,u,h,jw)in enumerate([(2,82,310,311,313,314,318,0),(86,96,330,331,333,334,338,1),(700,701,710,711,713,714,718,1)]):
 if j==2:
  for i,k in zip([y,Q,z,u,h],[330,331,333,334,338]):xw[i]=xw[k]
 def eq(n,terms):
  nm='harmonic'+str(j)+'.'+n
  fixed[nm]=norm(((e,0),0,m,v) for e,m,v in terms);rw[nm]=rw['harmonic'+str(jw)+'.'+n]
 eq('tSq',[(0,[y],1),(-2,[T,T],-1),(-1,[T],2*mid),(0,[],-mid**2)])
 eq('Q',[(0,[Q],1),(0,[y,y],-1),(0,[y],-q1),(0,[],-q0)])
 eq('L/Q',[(0,[Q,z],1),(0,[y],-l1),(0,[],-l0)])
 eq('u',[(0,[u,y],1),(0,[u],d),(0,[u,z],1),(-2,[T,T],-1),(0,[],-a*a),(0,[z,z],-c*c),(-1,[T],-2*a),(-1,[T,z],-2*c),(0,[z],-2*a*c)])
 eq('cap',[(0,[u,h],1),(0,[u,u],-1),(0,[u,300],-1),(2,[],-1)])
 eq('B',[(1,[B,u],2045**2),(0,[h,h],-816**2)])
units={900:(1,0),901:(-1,0),45:(0,1),101:(0,2)}
words=[{} for _ in range(3)]
for k in range(3):
 for m in combinations_with_replacement(units,k):
  e=tuple(sum(units[i][j]for i in m) for j in (0,1))
  for avail in range(k,3):words[avail].setdefault(e,m)
def graph(table,U):
 raw=[]
 def push(n,r):
  den=lcm(*(F(a).denominator for a in r.values()));g=reduce(gcd,(int(F(a)*den)for a in r.values()))
  raw.append((n,{k:int(F(a)*den)//g for k,a in r.items()if a}))
 for n,rr in table.items():
  out=Counter()
  for (e,c,m),a in rr.items():
   h=tuple(e[j]+sum(xw[i][j]for i in m)-rw[n][j]for j in (0,1))
   assert h in words[2-len(m)],(n,h,m)
   out[c,tuple(sorted(m+words[2-len(m)][h]))]+=a
  push(n,out)
 push('harmonic.guard',{(0,(900,901)):1,(0,()):-1});push('zSquared',{(0,(45,45)):1,(0,(101,)):-1})
 ret=[]
 for i,(n,rr) in enumerate(raw,1):
  h=Counter()
  for (c,m),b in rr.items():
   o=tuple(v for v in m if v!=900)
   for s in product([*((u,)for u in U),()],repeat=m.count(900)):
    h[c,tuple(sorted(o+sum(s,())))]+=b*(-len(U))**s.count(())
  lo=min(c for (c,m),v in h.items()if v)
  ret.append(dict(name=n.split("#")[0],id=i,shift=-lo,terms=[dict(parameterPower=c-lo,coefficient=str(v),monomial=m) for(c,m),v in sorted(h.items())if v]))
 ids=sorted({v for r in ret for t in r['terms']for v in t['monomial']});ren={v:i for i,v in enumerate(ids,1)}
 assert ids[0]==1 and all(xw[k]==(0,0) for k in (1,*U))
 for r in ret:
  for t in r['terms']:t['monomial']=[ren[v]for v in t['monomial']]
 return dict(input=1,variables=len(ids),rows=ret),ren
baseout,basemap=graph(base,[314,334])
assert baseout==read('donor165','QUADRICS.json') and {str(k):v for k,v in basemap.items()}==read('donor165','RENUMBER.json')
out,ren=graph(fixed,[314,334,714]);assert out['variables']==180 and len(out['rows'])==152
output('QUADRICS.json',out);output('RENUMBER.json',ren)
summ=Counter()
for r in out['rows']:
 for aa,bb in product(r['terms'],repeat=2):
  summ[tuple(sorted(aa['monomial']+bb['monomial'])),aa['parameterPower']+bb['parameterPower']]+=int(aa['coefficient'])*int(bb['coefficient'])
co={}
for (m,e),b in sorted(summ.items()):
 if b:co.setdefault(m,[]).append([e,str(b)])
assert co[(1,)*4]==[[0,'1']] and max(map(len,co))==4
terms=[[list(m),ds]for m,ds in co.items()]
# Fixed integer C=149^(2^763) is odd; signed balanced radix-C digits are UNIQUE.
# An in-memory power expansion would waste at least 2^763 bits per nonconstant coefficient.
assert max(abs(int(b)).bit_length()for ds in co.values()for e,b in ds)<2048
assert max(e for ds in co.values()for e,b in ds)<32
output('FIXED-QUARTIC.json',dict(arity=180,input=1,base={'integer':149,'exponent':{'integer':2,'exponent':763}},encoding='balanced-base digits: coefficient=sum(digit*base^position); ordered monomials use 1-based coordinates, repetitions are powers, [] is 1',terms=terms))
print('165 reproduced; fixed 180:',len(out['rows']),'rows;',len(terms),'monomials;',sum(map(len,co.values())),'nonzero balanced digits, max digit bits',max(abs(int(b)).bit_length()for ds in co.values()for e,b in ds))
