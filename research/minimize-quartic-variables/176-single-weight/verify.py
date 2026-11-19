import json,pathlib,hashlib,collections,itertools,math
from fractions import Fraction as F
src=pathlib.Path(__file__).with_name('DONOR-LAURENT.json'); q=pathlib.Path(__file__).parent;load=lambda p:json.loads(p.read_bytes()); C=load(q/'TRANSFER.json');assert hashlib.sha256(src.read_bytes()).hexdigest()==C['source_sha256'];p=load(q/'QUARTIC.json'); r=load(q/'QUADRICS.json'); ren={int(k):v for k,v in C['renumber'].items()}; inv={v:k for k,v in ren.items()}; assert sorted(inv)==list(range(1,177)) and ren[1]==1;w=C['weights']
def rule(ts):
 d=collections.Counter()
 for e,h,xs,a in ts:d[e,h,tuple(sorted(xs))]+=F(a)
 return {k:v for k,v in d.items() if v}
D={row['name']:rule([(t['unitPower'][0],t['parameterPower'],t['monomial'],t['coefficient']) for t in row['terms']]) for row in load(src)['rows']}
omit={'additive.detector%d.%s'%(i,s) for i in (0,1) for s in ['contactSquare','contactFourthPower','contactCombination','contactRelation']}|{'balanced.detector%d.poleInput.definition'%i for i in (0,1)}|{'detector1.normOver2w0.definition'}|{f'amplified.det1.product{j}.{a}.definition' for j in range(1,5) for a in (0,1)}|{f'new.det1.factor{j}.{a}' for j in range(5) for a in (0,1)}
assert len(omit)==len(omit & set(D))==29; D={k:v for k,v in D.items() if k not in omit}
def add(n,ts):D[n]=rule([(e,0,x,a)for e,x,a in ts])
A=list(map(F,['0','-1/2','-1','1/2399','-32/407']));L=[(-1)**j*sum(math.prod((1-v)**2 for v in comb) for comb in itertools.combinations(A,j)) for j in range(6)];assert L==list(map(F,C['coefficientsR']))
add('new.N2',[(0,[300],1),(2,[81,81],-1),(1,[],2)])
for i,(T,tid,P) in enumerate([(2,310,82),(86,330,96)]):
 t,y,s,g,f,m,z,d,h=range(tid,tid+9); 
 for n,eq in [('w',[(-1,[t,T],1),(0,[t],-1),(0,[],-1)]),('y',[(0,[y],1),(0,[t,t],-1)]),('y²',[(0,[s],1),(0,[y,y],-1)]),('mid',[(0,[g],1),(0,[],-L[2]),(0,[y],-L[3]),(0,[s],-L[4]),(0,[s,y],-L[5])]),('R',[(0,[f],1),(0,[],-1),(0,[y],-L[1]),(0,[s,g],-1)]),('h',[(0,[h],1),(0,[f,300],-1),(0,[],-1),(2,[f,f],-1)]),('B',[(1,[P,f],(5*409)**2),(0,[h,h],-(2*408)**2)])]: add('new.'+n+str(i),eq)
assert len(D)==148; s=collections.Counter(); observed=set()
for ro in r['rows']:
 ts=[];observed.update(v for t in ro['terms'] for v in t['monomial']); assert math.gcd(*(int(t['coefficient'])for t in ro['terms']))==1
 for t in ro['terms']:
  x=sorted(inv[v]for v in t['monomial']); assert len(x)<=2; v=[k for k in x if k not in [900,901]]; e=x.count(900)-x.count(901)-sum(w.get(f'x{j}_0',0) for j in v); ts.append((e,t['parameterPower'],v,t['coefficient']))
  for k in ro['terms']:
   s[(t['parameterPower']+k['parameterPower'],tuple(sorted(t['monomial']+k['monomial'])))]+=int(t['coefficient'])*int(k['coefficient'])
 if ro['id']==149:
  assert ro['id']==149 and rule(ts)=={} and {tuple(sorted(t['monomial'])) for t in ro['terms']}=={(),(175,176)};continue
 a=rule(ts);b=D.pop(list(D)[0]);ua,h,vs=min(a);ub,_,_=min(b);rat=a[min(a)]/b[min(b)]; assert {(e+ua-ub,h,vs):rat*k for (e,h,vs),k in b.items()}==a,ro['name']
assert not D and len(r['rows'])==149 and observed==set(inv);s={k:v for k,v in s.items() if v};pp={(k,tuple(m)):v for k,m,v in p['terms']};assert pp==s and len(pp)==len(p['terms']);print('PASS',len(pp),{k:v for (k,m),v in pp.items()if m==(1,1,1,1)},'generic monomials',len({m for k,m in pp}))
