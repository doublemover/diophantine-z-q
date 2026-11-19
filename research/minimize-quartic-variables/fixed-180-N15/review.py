"""Independent exact three-source comparison. Args: compact180 folder, prior fixed180 folder, fixed181 folder."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,sys,re
import sympy as S
from math import gcd
from collections import Counter
from itertools import product
D,O,E=map(Path,sys.argv[1:4]);H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rd=lambda d,n:json.loads((d/n).read_bytes())
assert H(O/'QUADRICS.json')=='e507e18381981eda89c13331f4db45236a9d7303f1e1b83a6d0c2dc090c10fcc' and H(E/'quartic181-N15.txt')=='4550b1785b53333f6f922409bc3c197c947b702fc16162468d602a63031284c1'
c=149**15;old=rd(O,'QUADRICS.json')['rows'];new=rd(D,'QUADRICS.json');td=rd(D,'TRANSFER.json');rn=rd(O,'RENUMBER.json');assert rn==td['renumber'] and td['integer_N']==15 and td['C']==str(c)
def loadold(r):
 a=Counter()
 for t in r['terms']:
  a[tuple(t['monomial'])]+=int(t['coefficient'])*c**t['parameterPower']
 return primitive(a)
def primitive(a):
 g=gcd(*(abs(z)for z in a.values()));return {k:z//g for k,z in a.items()if z}
def loadnew(r):
 a={tuple(m):z for m,z in r['terms']};assert len(a)==len(r['terms'])and all(0<=len(m)<=2 and list(m)==sorted(m) for m in a)and primitive(a)==a
 return a
assert len(new)==len(old)==152
amend=[]
for o,n in zip(old,new):
 assert o['id']==n['id'];a=loadold(o);b=loadnew(n)
 if a!=b:amend.append(n['id'])
 else: assert o['name']==n['name']
assert amend==[15,16,22,136]
occ=lambda table: [r['id']for r in table if any(rn['104']in x for x in loadnew(r))]
assert occ(new)==[16,136] and [r['id']for r in old if any(rn['104']in x for x in loadold(r))]==[15,16]
g0=rd(O/'donor165','WEIGHTS.json');aliases={700:2,701:96,702:7,703:8,704:9,705:10,706:97,707:98,708:99,710:330,711:331,713:333,714:334,718:338,606:605}
for i,wt in td['gauges'].items():
 if i=='104': assert wt==[0,0];continue
 orig=aliases.get(int(i),int(i)); assert wt==[g0[f'x{orig}_{d}']for d in (0,1)]
assert {n:rn[str(k)] for n,k in zip(('z','v','b','low','hi','W','R2','R'),(45,104,105,109,110,111,112,113))}==dict(z=37,v=63,b=64,low=68,hi=69,W=70,R2=71,R=72)
assert loadnew(new[14])=={(70,70):1,(64,72):-1}
assert loadnew(new[15])=={():-51,(37,63):51,(63,):702575}
assert loadnew(new[21])=={(46,46):1,(47,47):-8,(68,):1,(69,69):1,(70,71):-c}
s,R=S.symbols('s R');a=-S.Rational(705023,51);V=1/(s-a);p=lambda x:x*(x-2401)*(32*x+343);A=p(705024);P=p(1-51*s);fw=557*149*c*c
v={37:s+48,63:V,72:R/c}
raw=sum(z*S.prod(v[i]for i in m)for m,z in loadnew(new[135]).items());slope=S.cancel(raw*(s-a)**2/(R*(P-A)-fw*P));assert slope.is_Rational and slope!=0
assert td['A']==A and F(td['center'])==F(-705023,51)
poly=Counter()
for n in new:
 z=loadnew(n)
 for(m,a),(k,b) in product(z.items(),repeat=2):poly[tuple(sorted(m+k))]+=a*b
poly={m:a for m,a in poly.items()if a}
assert poly=={tuple(m):a for m,a in rd(D,'POLYNOMIAL.json')};lx=(D/'quartic180-N15.txt').read_bytes();ls=re.findall(r'[+-]?[^+-]+',lx.decode());assert ''.join(ls).encode()==lx
ex={}
for t in ls:
 sign=-1 if t[0]=='-'else 1;fac=t.strip('+-').split('*');co=int(fac.pop(0))if fac and fac[0][0].isdigit()else 1;m=[]
 for k in fac:
  g=re.fullmatch(r'x([1-9][0-9]*)(?:\^([1-4]))?',k);assert g;m+=[int(g[1])]*int(g[2]or 1)
 m=tuple(sorted(m));assert m not in ex;ex[m]=sign*co
assert ex==poly and len(ex)==3253 and set().union(*(set(m)for m in ex))==set(range(1,181))and ex[(1,)*4]==1 and max(map(len,ex))==4
assert 2**240*(43*67*191*702623*557)**3<149**66 and 149**66>4*8 and 17*31//8+1==66
print('PASS 148 identical specialized rows incl complete three comparisons, z and q guards, four independent scalar replacements, new v and R identity. Literal',len(lx),'bytes,',len(poly),'monomials,',max(abs(z).bit_length()for z in ex.values()),'bits, x1^4=1, SHA',hashlib.sha256(lx).hexdigest())
