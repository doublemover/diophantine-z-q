"""Independent of optimizer and builder: exact pullback, primitive rows, parameter roots and expansion."""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from math import gcd,isqrt
import json,hashlib
D=Path(__file__).resolve().parent
load=lambda n:json.loads((D/n).read_bytes())
src=load('brox193.quadratic-family.json');cert=load('certificate.json');tab=load('quadratic-family.json');poly=load('polynomial-family.json')
assert hashlib.sha1(b'blob '+str((D/'brox193.quadratic-family.json').stat().st_size).encode()+b'\0'+(D/'brox193.quadratic-family.json').read_bytes()).hexdigest()=='4ae582839923c88c0530bfd15b0b0a69562cd4d6'
ren={int(k):v for k,v in cert['renumber'].items()};assert sorted(ren.values())==list(range(1,193)) and ren[1]==1
U={int(k):tuple(v)for k,v in cert['oldunits'].items()};V={ren[int(k)]:tuple(v) for k,v in cert['units'].items()};w=cert['weights'];ws=lambda prefix,i:tuple(w[f'{prefix}{i}_{j}']for j in range(2));assert ws('x',1)==(0,0)
assert U=={63:(1,0),75:(0,1),76:(0,-1),77:(-1,-2),191:(0,-3),192:(1,-1),193:(-1,-1)}
assert [(ren[i],V[ren[i]])for i in range(194,200)]==list(zip(range(187,193),[(1,0),(-1,0),(1,-1),(1,1),(0,1),(-1,-1)]))
def pull(r,old):
 d=defaultdict(int);us=U if old else V
 for t in r['terms']:
  m=[];a,b=0,0
  for x in t['monomial']:
   if x in us: i,j=us[x]
   elif old:m.append(ren[x]);i,j=ws('x',x)
   else:m.append(x);i=j=0
   a+=i;b+=j
  if old:i,j=ws('r',r['id']);a-=i;b-=j
  d[(tuple(sorted(m)),t['parameterPower'],a,b)]+=int(t['coefficient'])
 return {k:v for k,v in d.items() if v}
R=tab['residuals']; assert len(R)==166 and len(src['residuals'])==167
for old,new in zip(src['residuals'][:162],R[:162],strict=True):
 assert old['id']==new['id'];a=pull(old,True);b=pull(new,False);assert a.keys()==b.keys() and len({F(a[k],b[k])for k in a})==1
def gr(r):return {tuple(t['monomial']):int(t['coefficient']) for t in r['terms'] if t['parameterPower']==0}
def reconcile(g,r):
 got=gr(r);assert set(g)==set(got) and len({F(g[k],got[k])for k in g})==1 and len(got)==len(r['terms'])
for g,r in zip([{(63,193):1,(76,):-1},{(75,76):1,():-1},{(63,77):1,(76,76):-1},{(75,191):1,(76,76):-1},{(63,76):1,(192,):-1}],src['residuals'][162:],strict=True):reconcile(g,r)
for g,r in zip([{(187,188):1,():-1},{(190,192):1,():-1},{(190,):1,(187,191):-1},{(189,191):1,(187,):-1}],R[162:],strict=True):reconcile(g,r)
E=defaultdict(int)
for r in R:
 ts=r['terms'];groups=defaultdict(dict)
 for k,t in enumerate(ts):
  m=tuple(t['monomial']);assert len(m)<=2;groups[m][t['parameterPower']]=int(t['coefficient'])
  for j,h in enumerate(ts[:k+1]):
   idx=t['parameterPower']+h['parameterPower'],tuple(sorted(m+tuple(h['monomial'])));E[idx]+=(1+(j!=k))*int(t['coefficient'])*int(h['coefficient'])
 c=gcd(*(abs(q[0])for q in groups.values()if q.keys()=={0}));p=gcd(*(abs(q[1])for q in groups.values()if q.keys()=={1}));assert c==1 or (gcd(c,p)==1 and c%149)
E={k:v for k,v in E.items() if v}
T={(t['parameterPower'],tuple(t['monomial'])):int(t['coefficient'])for t in poly['terms']};assert T==E and len(T)==len(poly['terms'])==2723 and T[0,(1,1,1,1)]==1
G=defaultdict(lambda:[0,0,0])
for (e,m),v in E.items():G[m][e]=v
for m,(c,b,a) in G.items():
 roots=[]
 if a:
  disc=b*b-4*a*c
  if disc>=0 and isqrt(disc)**2==disc:
   roots += [y//(2*a) for y in [-b+isqrt(disc),-b-isqrt(disc)] if y%(2*a)==0]
 elif b and c%b==0:roots=[-c//b]
 for y in roots:
  if y>=149:
   while y%149==0:y//=149
   assert y!=1
assert len(G)==2719 and set(x for m in G for x in m)==set(range(1,193));print('PASS: exact first 162 projective rows, old 5 and new 4 guards, 166 primitive quadrics, 192 coordinates, 2,719 monomials for every 149^N, N>=1; input fourth coefficient 1.')
