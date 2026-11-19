"""Invert the integer/unit coordinate transformations of the fixed 183 crossover."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from itertools import product
import hashlib,json,math,sys
P=Path(__file__).resolve().parent
base=Path(sys.argv[1]) if len(sys.argv)>1 else P
pre='' if len(sys.argv)>1 else 'DONOR184-'
def load(p):return json.loads(p.read_bytes())
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canon(eq):
 d=Counter()
 for e,ids,z in eq:d[e,tuple(sorted(ids))]+=z
 d={k:v for k,v in d.items()if v};anchor=min(d);return tuple(sorted((e-anchor[0],ids,Q(z)/d[anchor])for (e,ids),z in d.items()))
def dec(r,t):
 m={j:int(i)for i,j in t['renumber'].items()};gu={int(i):j[0]for i,j in t['units'].items()};sc={int(k):j for k,j in t['diagonal149'].items()};d=[]
 assert m[1]==1 and sc[1]==0 and t['weights']['x1_0']==0
 if r['name']=='guard.0':
  assert {tuple(m[k]for k in x):z for x,z in r['terms']}=={():-1,(900,901):1};return ()
 for x,z in r['terms']:
  y=[m[k]for k in x];v=[i for i in y if i not in gu]
  e=t['weights'][f"r{r['id']}_0"]+sum(gu.get(i,0)for i in y)-sum(t['weights'][f'x{i}_0']for i in v)
  d.append((e,v,z*Q(149)**(-sum(sc[k]for k in x))))
 return canon(d)
qr=base/(pre+'QUADRICS.json');tr=base/(pre+'TRANSFER.json')
assert h(qr)=='465676ee8bb298e11368e8d33f672f0bc7214b89a99bfd0b3dfb5b7f1ab49c37' and h(tr)=='be568044b9fcba6d6711fda4e43dd3cd69835a66204408585124009f49124df8'
old=load(qr);flow=load(tr)
drop=['scalar.rPair1.definition','scalar.four_contact_product.definition','scalar.forced_prime.definition','input.cleared']
common=Counter((r['name'],dec(r,flow))for r in old if r['name'] not in drop)
assert sum(common.values())==150
C=149**15
# P(s)=(1-51s)(-2400-51s)(375-1632s), A=P(-48).
def poly(s):return (1-51*s)*(-2400-51*s)*(375-1632*s)
A=poly(-48); a,b,d=4244832,-208805679,10215454581
assert A==9252635472
# Equality of degree-at-most-three polynomials from four distinct points.
assert all(A-poly(s)==(s+48)**2*(a*s+b)+(s+48)*d for s in [-48,0,1,2])
expected=list(common.elements()); expected += [('input.cleared',canon([(0,[17+j],-1),(0,[29+j],1),(0,[45,201+j],-51),(1,[201+j],1)]))for j in [0,1]]
expected += [('new.scalar.inverse',canon([(-1,[45,101],1),(0,[101],48),(0,[],-1)])),
 ('new.scalar.denominator',canon([(-1,[45],a),(0,[],b),(0,[101],d),(-2,[45,113],-Q(149,C)*a),(-1,[113],-Q(149,C)*b),(-1,[101,113],-Q(149,C)*d),(0,[101,101],-A)]))]
rows=load(P/'QUADRICS.json');t=load(P/'TRANSFER.json')
assert len(rows)==154 and [r['id']for r in rows]==list(range(1,155))
assert Counter((r['name'],dec(r,t))for r in rows)==Counter(expected)
zz=Counter()
for r in rows:
 terms=r['terms'];assert all(m==sorted(m) and len(m)<=2 and type(c)==int and c for m,c in terms)
 assert math.gcd(*(abs(c)for _,c in terms))==1 and len({tuple(m)for m,c in terms})==len(terms)
 for (m,x),(n,y)in product(terms,repeat=2):zz[tuple(sorted(m+n))]+=x*y
zz={k:v for k,v in sorted(zz.items())if v};assert list(zz.items())==[(tuple(m),v)for m,v in load(P/'POLYNOMIAL.json')]
assert set(i for m in zz for i in m)==set(range(1,184)) and max(map(len,zz))==4 and zz[1,1,1,1]==1
parts=[]
for m,z in zz.items():
 v=[f'x{i}'+(f'^{k}'if k>1 else'')for i,k in sorted(Counter(m).items())]
 if abs(z)!=1 or not v:v.insert(0,str(abs(z)))
 parts.append(('-'if z<0 else('+'if parts else''))+'*'.join(v))
raw=''.join(parts).encode();sha=hashlib.sha256(raw).hexdigest()
assert len(zz)==2666 and len(raw)==61579 and max(abs(x).bit_length()for x in zz.values())==293
assert raw==(P/'quartic183-N15.txt').read_bytes() and sha=='864f890336d97985b8b7285c2618ea0c61bcd39e6629a6d174603d55b07400de'
print('PASS 183 coordinates, 154 rows, 2666 monomials. Fixed N=15 literal:',sha)
