"""Fixed literal; no solver, remote access or new coefficients. Python >=3.9 + SymPy."""
from pathlib import Path
import sys,itertools,json,hashlib,math
from fractions import Fraction as F
from collections import Counter
import sympy as S
new=Path(__file__).resolve().parent; old=new/'donor182'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={
'QUADRICS.json':'896989a5c482837e1ff82c1ea1a82c8abfcb4d3c364e1aca7440d278fc6a9df5',
'POLYNOMIAL.json':'eb5d554595103fcd950bdab76ba6762255081efe51e4d6698e4c758b97721392',
'TRANSFER.json':'7367f19fb1867c96c03b8634275c71ebce12615971b5d7c3ba403484950449d0',
'quartic181-N15.txt':'4550b1785b53333f6f922409bc3c197c947b702fc16162468d602a63031284c1'}
for k,h in pins.items(): assert H(new/k)==h
assert H(old/'quartic182-N15.txt')=='773ca292f53ac13ec52484c8e6f2ee4cfc9b5bc216a84e80efbb0afd6d09d261'
for k,h in json.loads((old/'SHA256SUMS.json').read_bytes()).items():assert H(old/k)==h
def decode(d):
 rows=json.loads((d/'QUADRICS.json').read_bytes());tr=json.loads((d/'TRANSFER.json').read_bytes());w=tr['weights'];ds=tr['diagonal149'];rn={i:int(k)for k,i in tr['renumber'].items()};assert set(rn)==set(range(1,len(rn)+1)) and rn[1]==1 and w['x1_0']==ds['1']==0
 for u in (305,311,317):assert w[f'x{u}_0']==0
 # Explicit guard remains q^-1*(u0+u1+u2-3)=1, before we use it.
 guard=Counter()
 for m,a in rows[-1]['terms']:guard[tuple(sorted(rn[i]for i in m))]+=a*F(149)**-sum(ds[str(i)]for i in m)
 c=-guard[()]; assert c and dict(guard)=={():-c,(901,):-3*c,**{(u,901):c for u in(305,311,317)}}
 out=[]
 for r in rows:
  dic=Counter()
  for m,a in r['terms']:
   a=F(a)*F(149)**-sum(ds[str(i)]for i in m);m=[rn[i]for i in m];e=-m.count(901)-sum(w[f'x{i}_0']for i in m if i!=901)
   m1=tuple(i for i in m if i not in(317,901))
   for term in itertools.product(range(4),repeat=m.count(317)):
    k,j,l,n=(term.count(i)for i in range(4));dic[e+k,tuple(sorted(m1+(305,)*j+(311,)*l))]+=a*(-1)**(j+l)*3**n
  out.append((r['name'],norm(dic)))
 return out
def norm(d):
 d={k:F(v)for k,v in d.items()if v}
 if not d:return {}
 e,m=min(d); return {(j-e,n):v/d[e,m] for(j,n),v in d.items()}
O,N=decode(old),decode(new);names={'scalar.W2.definition','scalar.b.definition','scalar.cubicPole','parity_scalar.reduced_scalar.root.power4','scalar.reweightedOddComponent','new.scalar.inverse','new.scalar.denominator'}
same=[(n,p)for n,p in O if n not in names]; assert same==[(n,p)for n,p in N if n not in names] and len(same)==149
C=149**15;L=557*149**2;pol=lambda b:b*(b-2401)*(32*b+343);a=F(-705023,51);A=pol(705024)
def one(n):return next(p for k,p in N if k==n)
assert one('scalar.cubicPole')==norm({(0,(111,111)):1,(0,(105,113)):-1})
assert one('scalar.reweightedOddComponent')==norm({(0,(64,64)):1,(0,(65,65)):-8,(0,(110,110)):1,(1,(109,)):1,(0,(111,112)):-C})
q,s,v,r=S.symbols('q s v r');x={45:q*s,101:v,113:q*r/C}
def evalrow(n):return sum(co*q**e*S.prod(x[i]for i in m)for(e,m),co in one(n).items())
assert S.factor(evalrow('new.scalar.inverse').subs(v,1/(s-a)))==0
eq=evalrow('new.scalar.denominator').subs(v,1/(s-a))
r0=S.factor(F(L,149)*C**2*pol(1-51*s)/(pol(1-51*s)-A));assert S.factor(S.solve(eq,r)[0]-r0)==0
ratio=S.factor(eq/((pol(1-51*s)-A)*r-F(L,149)*C**2*pol(1-51*s)));assert S.factor(ratio*(s-a)**2).as_powers_dict().keys() <= {q} or all(i.is_Rational or i==q for i in S.factor(ratio*(s-a)**2).as_powers_dict())
P=lambda x:pol(1-51*x*x)
assert all(P(x)%149 and (P(x)-A)%149 for x in range(149))
def val(n,p):
 k=0
 while n%p==0:n//=p;k+=1
 return k
for p,mod,vals in [(2,64,{1,2,4,5}),(3,27,{2}),(17,17,{0})]:
 assert {val(P(x),p)for x in range(mod)}==vals and val(mod,p)>max(vals)
 assert val(A,p)-max(vals)>=(3 if p==2 else 1) and (557-149)%({2:8,3:3,17:17}[p])==0
assert 11*2412*343<A and P(0)==-900000 and P(1)<-900000
assert F(L,149)*C**2*900000/(A+900000)>2**20 and 2**100*F(1,2**20)**5<=1
D=43*67*191*557*702623
assert S.factorint(A)=={2:9,3:4,17:1,41:1,43:1,67:1,191:1,702623:1} and S.isprime(557)
assert 17*31//8+1==66 and 2**239*D**3<149**66
rows=json.loads((new/'QUADRICS.json').read_bytes());P4=Counter()
for row in rows:
 for (m,b),(n,c)in itertools.product(row['terms'],repeat=2):
  assert len(m)<=2
  P4[tuple(sorted(m+n))]+=b*c
P4={m:b for m,b in sorted(P4.items())if b};assert [[list(m),b]for m,b in P4.items()]==json.loads((new/'POLYNOMIAL.json').read_bytes())
txt=''
for m,b in P4.items():
 f=['x%d'%i+('^%d'%e if e>1 else '')for i,e in sorted(Counter(m).items())]
 if abs(b)!=1 or not f:f.insert(0,str(abs(b)))
 txt+=('-'if b<0 else '+'if txt else '')+'*'.join(f)
assert txt.encode()==(new/'quartic181-N15.txt').read_bytes() and (len(rows),len(P4),len(txt))==(153,3338,92690) and max(abs(b).bit_length()for b in P4.values())==307
assert P4[(1,)*4]==1 and {i for m in P4 for i in m}==set(range(1,182))
print('PASS 149 shared residuals incl all 3 measured poles and guarded q; 4 changed scalar rows; m149=31, a-depth≥66; exact 181/153/3338/307/92690.')
