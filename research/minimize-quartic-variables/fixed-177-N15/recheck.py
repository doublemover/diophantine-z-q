"""Independent fixed-177 residual, literal, and arithmetic check. No constructor imported."""
import itertools,collections,hashlib,math,re,json
from pathlib import Path
import sympy as s
from fractions import Fraction as F
D=Path(__file__).resolve().parent; parent=D/'donor178'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(parent/'QUADRICS.json')=='8f5f9b89fe3211107e31929b2b8934fd704b3d61139bd2f7928b67bcde5f69d0'
c=149**15; K=557*149**67
X=s.symbols('X:179')
def expr(r,dense):return sum(k*math.prod(X[x+(x>=71) if dense else x]for x in m) for m,k in r['terms'])
old=[None]+[expr(r,False)for r in json.loads((parent/'QUADRICS.json').read_bytes())]
rs=json.loads((D/'QUADRICS.json').read_bytes());new=[None]+[expr(r,True)for r in rs[:22]]+[None]+[expr(r,True)for r in rs[22:]]
w=X[72];q=X[129]+X[134]+X[176]-3;t=149*X[37]-7151
Y=s.Symbol('Y');T=s.Symbol('T')
fac=[(k,2401)for k in (117504,235008)]+[(k,2400)for k in (117504,235008)]+[(32*k,77175)for k in (117504,235008)]
P=math.prod(a*Y+b for a,b in fac)
lam=s.diff(P,Y).subs(Y,-1)/(2*P.subs(Y,-1))
def prop(a,b):
 ratio=s.cancel(a/b); assert ratio.is_Rational and ratio!=0,(a,b,ratio)
for i in range(1,151):
 if i==23: assert s.expand(old[i]-X[71]+c*w*w)==0; continue
 if i in (16,136):
  e=new[i].subs({X[37]:(T+7151)/149,X[60]:((T+7151)/149)**2})
  if i==16: prop(e,T*T*X[63]-1-lam*T)
  else:
   e=e.subs(X[63],(1+lam*T)/T**2);prop(e,T**2*(c*w-K*P.subs(Y,T-1)/T**6))
  continue
 adj=old[i]
 if i in (5,8,10,13,17,20,138,141):
  j={5:5,8:6,10:9,13:10,17:13,20:14,138:168,141:169}[i]
  prop(new[i],adj.subs({X[71]:c*w*w,X[j]:X[j]*w})/(w*w))
 elif i==22: prop(new[i],adj.subs({X[70]:X[70]/w,X[71]:c*w*w}))
 elif i in (32,33,34,35,36,37,38,39,40,41):
  adj=adj.subs({X[71]:c*w*w,X[83]:X[83]/q,X[84]:X[84]/q,X[85]:X[85]/w,X[86]:X[86]/w,X[178]:1/q},simultaneous=True)
  prop(new[i],adj*({34:w,35:w,36:q,37:q,40:q*q,41:q*q}.get(i,1)))
 else: prop(new[i],old[i])
# Role2 x(elt) is concretely the old register. Aggregate retained with positive moving weight.
for j, i in ((85,78),(86,137)):
 assert s.diff(old[i],X[j])==s.diff(new[i],X[j])==1
assert not any(any(X[j] in old[i].free_symbols for j in (85,86))for i in range(1,151) if i not in (32,33,34,35,38,39,78,137))
S={2,3,5,7,11,13,17,37,41,2399}
l=[a*(a-b) for a,b in fac]+[a*d-b*g for (a,b),(g,d) in itertools.combinations(fac,2)]
assert all(l)
G=math.prod(S|{149,557}|{p for n in l for p in s.factorint(abs(n))})
assert G==11379293055695063617230310849053151350305581051542357990
assert 149**126>2**175*G**4 and F(74712001,10**6)*2**68*3**16*5**16*7**4<2**149
assert all(min(a,b)>=1 and math.gcd(a*b,149)==1 for a,b in fac)
for a,b in fac:
 for p,k in ((2,3),(3,1),(17,1)):
  assert s.factorint(a)[p]-s.factorint(b).get(p,0)>=k
assert (557-149)%(8*3*17)==0
assert (F(15*67,8)>125 and F(15,8)>1)
# Safe height budget: L=2h(z)+h(w), z=(y+7152)/149, w=(K/C)*P/(1+y)^6.
assert 2**20>8*(14+math.log(7153))+math.log(64*K*P.subs(Y,1))
c0=149**126
assert F(8,2**25)+F(2**20,c0)<F(1,100) and F(1,2**25)+F(14+10,c0)<F(1,2)
assert 10_000*(F(360,100)+F(2500,c0))<c0
# Verify file polynomial independently from unordered pairs of residual terms.
p4=collections.Counter()
for r in rs:
 tr=r['terms'];assert math.gcd(*(v for m,v in tr))==1
 for k,(m,v) in enumerate(tr):
  assert len(m)<=2
  for n,u in tr[k:]:p4[tuple(sorted(m+n))]+=v*u*(1 if n==m else 2)
p4={m:v for m,v in p4.items()if v}
raw=(D/'quartic177-N15.txt').read_text(); terms=re.findall(r'[+-]?[^+-]+',raw);assert ''.join(terms)==raw
got={}
for a in terms:
 v=a.lstrip('+-').split('*');coef=1 if a[0]!='-'else -1
 if v[0].isdigit():coef*=int(v.pop(0))
 mon=[]
 for u in v:
  r=re.fullmatch(r'x([1-9][0-9]*)(?:\^([234]))?',u);assert r
  mon += [int(r[1])]*int(r[2] or 1)
 m=tuple(sorted(mon));assert m not in got;got[m]=coef
assert got==p4=={tuple(m):n for m,n in json.loads((D/'POLYNOMIAL.json').read_bytes())}
assert len(rs)==149 and {x for m in got for x in m}==set(range(1,178)) and max(map(len,got))==4 and got[(1,)*4]==1
print('PASS exact donor comparisons (moving aggregate and changed scalar distinguished), 6-factor H4.1 bounds, forward local base, weighted-height allowances, literal.')
print(len(got),max(abs(k).bit_length()for k in got.values()),len(raw),sha(D/'quartic177-N15.txt'))
