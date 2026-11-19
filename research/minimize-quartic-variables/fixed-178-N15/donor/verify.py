"""Standalone check of the fixed 180-variable polynomial and its two arithmetic seams."""
from pathlib import Path
from itertools import product
from collections import Counter
from fractions import Fraction as F
from math import gcd
import hashlib,json
p=Path(__file__).resolve().parent
files={'POLYNOMIAL.json':'758af1f5fd7088f2bf4769c2fa3d2e93329f2e70b24a4fcf22a979e40638f8b3','QUADRICS.json':'df3ecc34963e714f393a744a47bf4483c265da9ea228aaed8c7f74c3bdf59c79','TRANSFER.json':'2b07e167a2cf0bc185e4c6b057825942aaf3dedd6ff48768d6a8a575bdb50a7b','quartic180-N15.txt':'51d39c44672fa8a1a15940357a525babfa169794f460da30b5f186cd3e584d4a'}
assert all(hashlib.sha256((p/n).read_bytes()).hexdigest()==h for n,h in files.items())
rows=json.loads((p/'QUADRICS.json').read_bytes());tab=json.loads((p/'TRANSFER.json').read_bytes())
assert tab['integer_N']==15 and int(tab['C'])==149**15 and tab['effective_point_label']=='X^2+48' and tab['center']=='-705023/51'
ren={int(k):v for k,v in tab['renumber'].items()};inv={v:k for k,v in ren.items()};assert len(ren)==len(inv)==180 and ren[1]==1
def rec(n):return next({tuple(sorted(inv[i]for i in m)):v for m,v in row['terms']}for row in rows if row['name']==n)
def same(f,g):
 assert set(f)==set(g);k=next(iter(f));assert f[k] and g[k] and all(f[j]*g[k]==g[j]*f[k]for j in f)
s0=F(-705023,51)
def P(b):return b*(b-2401)*(32*b+343)
p3=-51*(-51)*(-1632);p2=(-51)*(-51)*375+(-51)*(-2400)*(-1632)+1*(-51)*(-1632);p1=(-51)*(-2400)*375+1*(-51)*375+1*(-2400)*(-1632)
b=-p3;c=-p2-2*s0*p3;d=-p1-2*s0*p2-3*s0**2*p3;A=P(705024);L=557*149**2;C=149**15
same(rec('saturated.scalar.interpolationInverse'),{(45,104):1,(104,):-48-s0,():-1})
same(rec('scalar.cubicPole'),{(111,111):1,(105,113):-1})
same(rec('scalar.reweightedOddComponent'),{(64,64):1,(65,65):-8,(110,110):1,(109,):1,(111,112):-C})
T=F(149,L*C);same(rec('saturated.scalar.denominator'),{(45,):b,():c-48*b,(104,):d,(45,113):-b*T,(113,):-(c-48*b)*T,(104,113):-d*T,(104,104):-A})
same(rec('harmonic.guard'),{(314,901):1,(334,901):1,(714,901):1,(901,):-3,():-1});same(rec('zSquared'),{(45,45):1,(101,):-1})
pol=Counter()
for k,r in enumerate(rows,1):
 assert r['id']==k and gcd(*(v for m,v in r['terms']))==1 and all(len(m)<=2 for m,v in r['terms'])
 for (a,v),(b,w)in product(r['terms'],repeat=2):pol[tuple(sorted(a+b))]+=v*w
pol={m:a for m,a in sorted(pol.items())if a}
assert [[list(m),v]for m,v in pol.items()]==json.loads((p/'POLYNOMIAL.json').read_bytes()) and {i for m in pol for i in m}==set(range(1,181)) and pol[(1,)*4]==1
def term(m,v):
 f=[f'x{i}'+(f'^{e}'if e>1 else '')for i,e in sorted(Counter(m).items())]
 if not f or abs(v)!=1:f.insert(0,str(abs(v)))
 return ('-'if v<0 else '+')+'*'.join(f)
assert ''.join(term(m,v)for m,v in pol.items()).lstrip('+').encode()==(p/'quartic180-N15.txt').read_bytes()
assert (len(rows),len(pol),max(abs(v).bit_length()for v in pol.values()))==(152,3253,365)
def v(n,p):
 assert n
 k=0
 while n%p==0:n//=p;k+=1
 return k
for pr,mod,tgt in ((2,64,{1,2,4,5}),(3,27,{2}),(17,17,{0})):
 assert {v(P(1-51*x*x),pr)for x in range(mod)}==tgt and max(tgt)<v(mod,pr)
assert all(P(1-51*x*x)%149 not in(0,A%149)for x in range(149))
assert A==2**9*3**4*17*41*43*67*191*702623 and v(A,149)==0
D=43*67*191*557*702623
assert 2**240*D**3<149**66 and 149**66>4*2450 and 17*31//8+1==66 and 557*149*C*C*900000>2**20*(A+900000)
print('PASS exact 180/152/3253/365; 82777-byte literal; four changed rows, both guards, 31→66 and signed height budget. No access to solver, network or Lean.')
