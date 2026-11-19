"""Exact portable replay of explicit shared-weight quartics; standard library only."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter,defaultdict
from itertools import combinations,product
from hashlib import sha256
import json,math
p=Path(__file__).resolve().parent
def load(n):return json.loads((p/n).read_bytes())
def sh(n):return sha256((p/n).read_bytes()).hexdigest()
assert sh('DONOR229.json')=='f0e6fc3f62525d7b251a10fc5f4cf0e6663c3f6f08beeef3cb28092b2e1555a8'
assert sh('DONOR193-LAURENT.json')=='d14f1031ed3306e228fbf2b019654b6f8c41382c2fd571775130500d1ae418f1'
tr=load('TRANSFER.json');ren={int(i):j for i,j in tr['renumber'].items()};iv={j:i for i,j in ren.items()};n=len(iv);assert n==184 and set(iv)==set(range(1,n+1)) and iv[1]==1
old={77:1,78:-1,90:0,91:0,92:-1,204:0,205:0,206:-1};units={int(i):u[0]for i,u in tr['units'].items()};assert set(units.values())=={1,-1} and len(units)==2
exclude=set(range(22,27))|{28}|set(range(34,42))|set(range(83,101))|set(range(176,184))|set(range(189,207));assert 'skip' not in tr
D={}
def ins(name,ts):
 d=defaultdict(Q)
 for e,m,z in ts:d[e,tuple(sorted(m))]+=Q(z)
 D[name+chr(64)+str(len(D)+1)]={k:z for k,z in d.items()if z}
V=load('DONOR193-LAURENT.json')['rows']; by={r['group']:r for r in V}
def marks(r):return [(t['unitPower'][0],t['monomial'],Q(t['coefficient'])*Q(149)**(15*t['parameterPower']))for t in r['terms']]
def om(n):return ('contact' in n and n.startswith('additive.detector') or n.startswith(('balanced.detector','new.det1.factor','amplified.det1.product','detector1.normOver2w0')) or n=='new.aggregate')
for r in V:
 if not om(r['group']) and not r['group'].startswith(('new.det0.factor','amplified.det0.product','amplified.C1.power4','cleared.E1.square','cleared.E2.square','cleared.E3.square','cleared.E4.square','homogeneous.H.square','input.cleared.square','input.cleared.fourth')):ins(r['group'],marks(r))
# Compare each new physical factor to the certified 170 row before rational normalization.
assert sh('MIXED170-QUADRICS.json')=='9d02542ceece35b0b9441a2bae500b5890d9e859d1b6b315446ff41434977215' and sh('MIXED170-TRANSFER.json')=='e268255c5a3f3be66de550ccbd2a0d2f4a4876551a6516c851cf4c4b869b5378'
mtr=load('MIXED170-TRANSFER.json'); mi={j:int(i)for i,j in mtr['renumber'].items()}; mu={int(i):u[0]for i,u in mtr['units'].items()}
for r in load('MIXED170-QUADRICS.json')['rows']:
 name=r['name']
 if not name.startswith(('rebuilt.factor.','chain')):continue
 terms=[]
 for t in r['terms']:
  vv=[mi[k]for k in t['monomial']];xs=[k for k in vv if k not in mu]
  e=sum(mu.get(k,0)for k in vv)-sum(mtr['weights'][f'x{k}_0']for k in xs)+mtr['weights'][f"r{r['id']}_0"]
  terms.append((e,[k if not 400<=k<500 else k+300 for k in xs],Q(t['coefficient'])*Q(149)**(15*t['parameterPower'])))
 ins('mixed170.'+name,terms)
real=[(0,[192],1)];imag=[(0,[193],1)]
for z in [201,213,225]:
 for v in [z,z+2,z+8]:
  real += [(1,[z+8,v],1),(1,[z+9,v+1],2)];imag += [(1,[z+8,v+1],1),(1,[z+9,v],1)]
ins('v62.aggregate.real',[(0,[2],2),(0,[86],-2),(1,[],26)]+real)
ins('v62.aggregate.imag',[(0,[2],2),(0,[86],-4),(0,[410],2),(1,[],-8)]+imag)
rename={7:421,8:422,9:423,10:424,96:420,97:425,98:426,99:427}
for r in V:
 name=r['group']
 if name.startswith('detector1.')and 'normOver' not in name:ins(name.replace('detector1.','detector2.'),[(e,[rename.get(i,i)for i in m],z)for e,m,z in marks(r)])
# Exact independent scalar/reference projection against the effective 229 donor.
def pn(ts):
 a=defaultdict(Q)
 for e,m,z in ts:a[e,tuple(sorted(m))]+=Q(z)
 a={k:z for k,z in a.items()if z};(e0,m0),z0=min(a.items());return {(e-e0,m):z/z0 for(e,m),z in a.items()}
for r in load('DONOR229.json')['residuals']:
 if r['id']not in [1,*range(47,61),*range(101,107),*range(155,171),173,174]:continue
 assert pn(marks(by[r['name']]))==pn([(sum(old.get(x,0)for x in t['monomial']),[x for x in t['monomial']if x not in old],int(t['coefficient'])*Q(149)**(15*t['parameterPower']))for t in r['terms']]),r['name']
theta=list(map(Q,('0','-1/2','-1','1/2399','-32/407')));b=[(Q(3,22)-t)**2 for t in theta];a=[(-1)**k*sum(map(math.prod,combinations(b,k)))for k in range(6)];assert list(map(Q,tr['a']))==a
ins('shared.NsquareMinusTwoQ',[(0,[300],1),(2,[81,81],-1),(1,[],2)])
for j,(T,B) in enumerate([(2,82),(86,96),(410,420)]):
 w,y,s,v,R,h=range(301+j*6,307+j*6);pref='d'+str(j)+'.'
 ins(pref+'inv',[(-1,[w,T],1),(0,[w],-Q(3,22)),(0,[],-1)])
 ins(pref+'y',[(0,[y],1),(0,[w,w],-1)])
 if n==195:
  ins(pref+'y2',[(0,[s],1),(0,[y,y],-1)])
  ins(pref+'mid',[(0,[v],1),(0,[],-a[2]),(0,[y],-a[3]),(0,[s],-a[4]),(0,[s,y],-a[5])])
  ins(pref+'ratio',[(0,[R],1),(0,[],-a[0]),(0,[y],-a[1]),(0,[s,v],-1)])
 else:
  al=a[4]/(2*a[5]);be=(a[3]/a[5]-al**2)/2
  ins(pref+'v',[(-1,[T,v],1),(0,[v],-Q(3,22)),(0,[y,y],-1),(0,[y],-al),(0,[],-be)])
  ins(pref+'ratio',[(0,[R],1),(0,[v,v],-a[5]),(0,[y,y],-a[2]+2*a[5]*al*be),(0,[y],-a[1]+a[5]*be**2),(0,[],-a[0])])
 ins(pref+'H',[(0,[h],1),(0,[R,300],-1),(0,[],-1),(2,[R,R],-1)])
 ins(pref+'B',[(1,[B,R],2045**2),(0,[h,h],-816**2)])
ps={int(i):j for i,j in tr['diagonal149'].items()};assert set(ps)==set(iv) and ps[1]==0
W=tr['weights'];assert W['x1_0']==0
out=load('QUADRICS.json');assert len(out)==len(D)+1==155
poly=defaultdict(int);obs=set()
for num,r in enumerate(out,1):
 assert r['id']==num
 coeff={tuple(m):z for m,z in r['terms']};assert len(coeff)==len(r['terms']) and math.gcd(*coeff.values())==1
 assert max(map(len,coeff))<=2 and all(z and list(m)==sorted(m)for m,z in coeff.items())
 for m in coeff:obs.update(m)
 for (m,z),(l,h)in product(coeff.items(),repeat=2):poly[tuple(sorted(m+l))]+=z*h
 if r['name']=='guard.0':
  assert {tuple(iv[i]for i in m):z for m,z in coeff.items()}=={():-1,(900,901):1};continue
 d=defaultdict(Q)
 for m,z in coeff.items():
  pvars=tuple(iv[i]for i in m if iv[i]not in units)
  e=sum(units[iv[i]]for i in m if iv[i]in units)-sum(W['x'+str(i)+'_0']for i in pvars)+W['r'+str(num)+'_0']
  d[e,pvars]+=Q(z)*Q(149)**(-sum(ps[i]for i in m))
 d={k:z for k,z in d.items() if z};wanted=D.pop(r['name']+'@'+str(num));assert set(d)==set(wanted),r['name']
 mult=d[min(d)]/wanted[min(d)];assert mult and all(d[k]==mult*z for k,z in wanted.items()),r['name']
assert not D and obs==set(iv)
poly={m:z for m,z in poly.items() if z};data=load('POLYNOMIAL.json');assert len(data)==len(poly) and {tuple(m):z for m,z in data}==poly and poly[(1,1,1,1)]==1 and max(map(len,poly))==4
literal=''
for m,z in sorted(poly.items()):
 f=[f'x{i}'+(f'^{k}'if k>1 else'')for i,k in sorted(Counter(m).items())]
 if abs(z)!=1 or not f:f.insert(0,str(abs(z)))
 literal+=('-'if z<0 else('+'if literal else''))+'*'.join(f)
assert literal.encode()==(p/f'quartic{n}-N15.txt').read_bytes() and len(literal)<100000
print(json.dumps(dict(N=15,variables=n,witnesses=n-1,quadrics=len(out),monomials=len(poly),bytes=len(literal),literal_sha256=sh(f'quartic{n}-N15.txt'),height=max(map(abs,poly.values())),input_fourth_power=1),indent=2))
