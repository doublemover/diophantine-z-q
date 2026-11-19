import json,pathlib,hashlib,collections,itertools,math
from fractions import Fraction as F
q=pathlib.Path(__file__).resolve().parent;src=q.parents[1]/'170-eight-mixed-factors'/'DONOR-LAURENT.json';load=lambda p:json.loads(p.read_bytes()); C=load(q/'TRANSFER.json');assert hashlib.sha256(src.read_bytes()).hexdigest()==C['source_sha256'];r=load(q/'QUADRICS.json'); ren={int(k):v for k,v in C['renumber'].items()}; inv={v:k for k,v in ren.items()}; assert sorted(inv)==list(range(1,190)) and ren[1]==1;w=C['weights']
def rule(ts):
 d=collections.Counter()
 for e,h,xs,a in ts:d[e,h,tuple(sorted(xs))]+=F(a)
 return {k:v for k,v in d.items() if v}
D={row['name']:rule([(t['unitPower'][0],t['parameterPower'],t['monomial'],t['coefficient']) for t in row['terms']]) for row in load(src)['rows']}
omit={'additive.detector%d.%s'%(i,s) for i in (0,1) for s in ['contactSquare','contactFourthPower','contactCombination','contactRelation']}|{'balanced.detector%d.poleInput.definition'%i for i in (0,1)}|{'detector1.normOver2w0.definition'}|{f'amplified.det1.product{j}.{a}.definition' for j in range(1,5) for a in (0,1)}|{f'new.det1.factor{j}.{a}' for j in range(5) for a in (0,1)}
assert len(omit)==len(omit & set(D))==29; D={k:v for k,v in D.items() if k not in omit}
def add(n,ts):D[n]=rule([(e,0,x,a)for e,x,a in ts])
# Third actual pole and full-field second component, not merely a third formal radical.
for n in ('p2.definition','firstConic','Bh.definition','q2.definition','secondConic'):
 srcname='detector1.'+n;dest='detector2.'+n
 ids={7:410,8:411,9:412,10:413,96:414,97:415,98:416,99:417}
 D[dest]={(e,c,tuple(sorted(ids.get(x,x)for x in xs))):v for (e,c,xs),v in D[srcname].items()}
comp=[(0,[193],-1),(1,[420],1)]
for f in (201,213,225):
 h=f+8
 for i in (f,f+2,h):
  comp.extend([(1,[h,i+1],-1),(1,[h+1,i],-1)])
add('new.imaginaryTrace',comp)
add('new.thirdArgument',[(0,[421],1),(0,[86],-1),(1,[],-8),(1,[420,420],-1)])
A=list(map(F,['0','-1/2','-1','1/2399','-32/407']));L=[(-1)**j*sum(math.prod((1-v)**2 for v in comb) for comb in itertools.combinations(A,j)) for j in range(6)];assert L[::-1]==list(map(F,C['coefficientsR']))
L=L[::-1]
add('new.N2',[(0,[300],1),(2,[81,81],-1),(1,[],2)])
for i,(T,tid,P) in enumerate([(2,310,82),(86,330,96),(421,350,414)]):
 t,y,s,g,f,m,z,d,h=range(tid,tid+9); 
 for n,eq in [('y',[(0,[y],1),(-2,[T,T],-1),(-1,[T],2),(0,[],-1)]),('y²',[(0,[s],1),(0,[y,y],-1)]),('mid',[(0,[g],1),(0,[],-L[2]),(0,[y],-L[3]),(0,[s],-L[4]),(0,[s,y],-L[5])]),('R',[(0,[f],1),(0,[],-L[0]),(0,[y],-L[1]),(0,[s,g],-1)]),('h',[(0,[h,g],1),(0,[f,300],-1),(0,[],-1),(2,[f,f],-1)]),('B',[(1,[P,f],(5*409)**2),(0,[h,h],-(2*408)**2)])]: add('new.'+n+str(i),eq)
assert len(D)==159; s=collections.Counter(); observed=set()
for ro in r['rows']:
 ts=[];observed.update(v for t in ro['terms'] for v in t['monomial']); assert math.gcd(*(int(t['coefficient'])for t in ro['terms']))==1
 for t in ro['terms']:
  x=sorted(inv[v]for v in t['monomial']); assert len(x)<=2; v=[k for k in x if k not in [900,901]]; e=x.count(900)-x.count(901)-sum(w.get(f'x{j}_0',0) for j in v); ts.append((e,t['parameterPower'],v,t['coefficient']))
  for k in ro['terms']:
   s[(t['parameterPower']+k['parameterPower'],tuple(sorted(t['monomial']+k['monomial'])))]+=int(t['coefficient'])*int(k['coefficient'])
 if ro['id']==160:
  assert ro['id']==160 and rule(ts)=={} and {tuple(sorted(t['monomial'])) for t in ro['terms']}=={(),(188,189)};continue
 a=rule(ts);b=D.pop(list(D)[0]);ua,h,vs=min(a);ub,_,_=min(b);rat=a[min(a)]/b[min(b)]; assert {(e+ua-ub,h,vs):rat*k for (e,h,vs),k in b.items()}==a,ro['name']
assert not D and len(r['rows'])==160 and observed==set(inv)
# Verify elementary effective constants separately without floating-point logarithms.
def primes(n):
 sv=bytearray([1])*(n+1);sv[:2]=b'\x00\x00'
 for i in range(2,math.isqrt(n)+1):
  if sv[i]:sv[i*i:n+1:i]=bytes((n-i*i)//i+1)
 return [i for i in range(n+1)if sv[i]]
ps=primes(76176);P=2029147*math.prod(ps);assert len(ps)==7499 and P.bit_length()==109466
Theta=[F(x)for x in ('0','-1/2','-1','1/2399','-32/407')]; exc=2029147*math.prod(ps);allowed=[2,3,5,7,11,13,37,41,47,67,109,179,257,439,2099,2399,2029147]
for u in Theta:
 for v in Theta:
  z=u-(2-v)
  for g in map(abs,(z.numerator,z.denominator)):
   for ell in allowed:
    while g%ell==0:g//=ell
   assert g==1
L=(9*(2*16384-1))//4+1;assert L==73726 and (7*L)==516082
assert 2**(4*246330)>(2*191102976)**4*P**9 and (2**246342)**8>(256*2**246331)**8*14**3
assert 9793*21**2<17*100**6
print('PASS: all 189-coordinate donor rows reconstructed and numerical cutoffs checked.')
