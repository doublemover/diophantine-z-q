"""Read a fixed181 directory and an independently reviewed fixed182 directory. No author imports."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
from math import gcd, isqrt
import hashlib,sys,json,re
import sympy as S
dn,base=map(Path,sys.argv[1:3]); rd=lambda d,n:json.loads((d/n).read_bytes())
def unpack(d):
 t=rd(d,'TRANSFER.json');ren={int(b):int(a) for a,b in t['renumber'].items()};diag=t['diagonal149']; wt=t['weights']
 assert ren[1]==1 and diag['1']==wt['x1_0']==0
 rows={}
 for r in rd(d,'QUADRICS.json'):
  z=Counter()
  for m,k in r['terms']:
   a=F(k)*F(149)**-sum(diag[str(i)]for i in m)
   ids=[ren[i]for i in m]
   ex=ids.count(900)-ids.count(901)-sum(wt[f'x{i}_0'] for i in ids if i not in (900,901)); uns=[i for i in ids if i not in (317,900,901)]
   # eliminate third harmonic via u2=q+3-u0-u1
   for tail in product((0,3,305,311),repeat=ids.count(317)):
    mon=tuple(sorted(uns+[i for i in tail if i>3]))
    z[ex+tail.count(0),mon]+=a*3**tail.count(3)*(-1)**sum(i>3 for i in tail)
  z={m:v for m,v in z.items()if v}; e=min(z) if z else (0,())
  label=r['name'] if r['name'] not in rows else r['name']+'@second'; assert label not in rows; rows[label]={(f-e[0],m):v/z[e]for(f,m),v in z.items()}
 return rows
o=unpack(base);n=unpack(dn);same={k for k in o.keys()&n.keys()if n[k]==o[k]}
assert len(o)==154 and len(n)==153 and len(same)==149 and 'q.guard'in same and 'input.cleared'in same
C=149**15
k='scalar.reweightedOddComponent'
assert n[k]=={(0,(64,64)):1,(0,(65,65)):-8,(0,(110,110)):1,(0,(111,112)):-C,(1,(109,)):1}
assert n['scalar.cubicPole']=={(0,(105,113)):1,(0,(111,111)):-1}
assert n['new.scalar.inverse']=={(1,()):-1,(0,(45,101)):1,(1,(101,)):F(705023,51)}
s,q,R=S.symbols('s q R');aa=-S.Rational(705023,51);L=557*149**2;p=lambda b:b*(b-2401)*(32*b+343);A=p(705024);P=p(1-51*s)
ds={45:q*s,113:R*q/C,101:1/(s-aa)}
den=sum(q**e*v*S.prod(ds[i]for i in m) for (e,m),v in n['new.scalar.denominator'].items());match=S.factor(den*(s-aa)**2/(R*(P-A)-S.Rational(L*C*C,149)*P))
assert not (match/q**2).free_symbols and match!=0,match
# reconstruct actual integral polynomial; parse decimal ASCII separately
rows=rd(dn,'QUADRICS.json');z=Counter()
for row in rows:
 assert gcd(*(k for m,k in row['terms']))==1 and all(len(m)<=2 for m,k in row['terms'])
 for((m,a),(r,b)) in product(row['terms'],repeat=2):z[tuple(sorted(m+r))]+=a*b
c={m:x for m,x in z.items()if x}
assert c=={tuple(m):x for m,x in rd(dn,'POLYNOMIAL.json')}
raw=(dn/'quartic181-N15.txt').read_bytes();terms=re.findall(r'[+-]?[^+-]+',raw.decode());assert ''.join(terms).encode()==raw
ex={}
for t in terms:
 sign=-1 if t[0]=='-'else 1; fac=t.strip('+-').split('*'); cz=int(fac.pop(0))if fac and fac[0][0].isdigit()else 1;m=[]
 for v in fac:
  g=re.fullmatch(r'x([1-9][0-9]*)(?:\^([1-4]))?',v);assert g;m.extend([int(g[1])]*int(g[2]or 1))
 m=tuple(sorted(m));assert m not in ex;ex[m]=sign*cz
assert c==ex and c[(1,)*4]==1 and set().union(*(set(m) for m in c))==set(range(1,182))
a=p(705024); bad={2:9,3:4,17:1,41:1,43:1,67:1,191:1,702623:1};assert a==S.prod(j**k for j,k in bad.items())and all(j>1 and all(j%f for f in range(2,isqrt(j)+1))for j in list(bad)+[557]);assert all(p(1-51*i*i)%149 not in {0,a%149} for i in range(149))
def vp(x,p):
 assert x!=0; k=0
 while x%p==0:x//=p;k+=1
 return k
for pr,mod,vs in ((2,64,{1,2,4,5}),(3,27,{2}),(17,17,{0})):
 assert {vp(p(1-51*i*i),pr) for i in range(mod)}==vs
d=43*67*191*702623*557;assert 2**240*d**3<149**66 and 17*31//8+1==66 and 557*149*C*C*900000>2**20*(a+900000)
print('PASS 149 identical donor rows; four actual replacements; verified cubic ratio and spectrum; literal',len(raw),'bytes',len(c),'terms, input^4=1, max',max(abs(x).bit_length()for x in c.values()),'bits. 31→66; 2^238 D^3<149^66/4. digest',hashlib.sha256(raw).hexdigest())
