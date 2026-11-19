"""Independent reverse map, never imports the author builder. Expects sealed folder path as argv[1]."""
import sys,json,hashlib,itertools
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
from functools import lru_cache
import sympy as s
here=Path(__file__).resolve().parent
if len(sys.argv)>1: d=Path(sys.argv[1])
elif (Path.cwd()/'FIXED-QUARTIC.json').exists(): d=Path.cwd()
elif (here/'FIXED-QUARTIC.json').exists(): d=here
else: raise SystemExit('Supply the fixed-180 packet directory as argv[1].')
src=d/'donor165'
assert hashlib.sha256((src/'QUADRICS.json').read_bytes()).hexdigest()=='4d7336a4efc970cf4f0e7677a9ecc0578a9884ee5676dbee4910ec444eee38af'
rd=lambda dr,k:json.loads((dr/k).read_text())
ser=lambda expr:s.sympify(expr)
Q,Z,C=s.symbols('q z C',nonzero=True)
@lru_cache(None)
def X(i):return s.Symbol('v'+str(i))
oldW=rd(src,'WEIGHTS.json')
aliases={700:2,701:96,702:7,703:8,704:9,705:10,706:97,707:98,708:99,710:330,711:331,713:333,714:334,718:338,606:605}
def rw(i,j):
 return oldW[f'x{aliases.get(i,i)}_{j}']
def canonical(f):
 f=s.expand(f)
 if not f:return ()
 terms=f.as_ordered_terms();EE=[]
 for t in terms:
  a,mon=t.as_coeff_Mul();p=mon.as_powers_dict();wt=tuple(int(p.get(v,0)) for v in (Q,Z,C))
  v=mon/Q**wt[0]/Z**wt[1]/C**wt[2]
  EE.append((str(v),wt,a))
 # allow multiplying whole rows only by a rational or powers of q,z,C.
 mins=tuple(min(wt[j] for _,wt,a in EE) for j in range(3))
 es=sorted((v,tuple(wt[j]-mins[j] for j in range(3)),a) for v,wt,a in EE)
 return tuple((v,wt,a/es[0][2])for v,wt,a in es)
def unpack(dr,new):
 qtab=rd(dr,'QUADRICS.json');ren=rd(dr,'RENUMBER.json');iv={v:int(k)for k,v in ren.items()};assert iv[1]==1
 def v(i):
  if i==901:return 1/Q
  if i==45:return Z
  if i==101:return Z**2
  if i==314:return Q+(3-X(714) if new else 2)-X(334)
  return X(i)*Q**-rw(i,0)*Z**-rw(i,1)
 nn=Counter();o={}
 for r in qtab['rows']:
  n=r['name'];nn[n]+=1;tag=n if nn[n]==1 else n+'#'+str(nn[n])
  raw=sum(int(t['coefficient'])*C**t['parameterPower']*s.prod(v(iv[k]) for k in t['monomial']) for t in r['terms'])
  o[tag]=raw
 # prior torus substitutions were legitimate for forward reconstruction only after these exact equations
 def g(r):return {tuple(sorted(iv[k] for k in t['monomial'])):int(t['coefficient']) for t in r['terms'] if t['parameterPower']==0}
 assert all(t['parameterPower']==0 for r in qtab['rows'][-2:]for t in r['terms'])
 assert g(qtab['rows'][-2])=={(i,901):1 for i in ([314,334,714] if new else [314,334])}|{(901,):-(3 if new else 2),():-1}
 assert g(qtab['rows'][-1])=={(45,45):1,(101,):-1}
 return o,v
old,_=unpack(src,False);new,decode=unpack(d,True)
changed=lambda n:n in ['new.firstTrace','new.aggregate','harmonic.guard','zSquared'] or n.startswith(('harmonic0.','harmonic1.'))
keep=[n for n in old if not changed(n)]
for n in keep:assert canonical(new[n])==canonical(old[n]),n
assert len(keep)==123
# Explicit physical definitions checked independently of row weights. u0 is removed by the true q relation.
def raw(i):
 if i==314:return Q+3-X(334)-X(714)
 return X(i)
t=s.Rational(3,22);roots=sorted((i-t)**2 for i in [0,-1,s.Rational(-1,2),s.Rational(1,2399),s.Rational(-32,407)])
y=s.symbols('y');q=s.prod(y-h for h in roots[:2]);g=s.prod(y-h for h in roots[2:]);D,L=s.div(g,q,y);c=-2399;A=s.Rational(584793232723,144506164)
tested=set(keep)
for offset,T,port,off,H in [(0,2,82,310,318),(1,86,96,330,338),(2,700,701,710,718)]:
 x=raw(T)/Q-t;y0=raw(off);qo=raw(off+1);w=raw(off+3);u=raw(off+4);h=raw(H)
 forms=[y0-x*x,qo-q.subs(y,y0),qo*w-L.subs(y,y0),u*(D.subs(y,y0)+w)-(x+A+c*w)**2,u*h-u*u-raw(300)*u-Q*Q,2045**2*Q*raw(port)*u-816**2*h*h]
 for name,expr in zip(('tSq','Q','L/Q','u','cap','B'),forms):
  n=f'harmonic{offset}.'+name;assert canonical(new[n])==canonical(expr),n;tested.add(n)
mp={96:701,7:702,8:703,9:704,10:705,97:706,98:707,99:708}
for n in ['p2.definition','firstConic','Bh.definition','q2.definition','secondConic']:
 n1='detector1.'+n;n2='detector2.'+n
 assert canonical(new[n1].xreplace({X(i):X(j) for i,j in mp.items()}))==canonical(new[n2]),n
 tested.add(n2)
# Assemble S using actual h(h+s+t), independent of the code for either aggregate.
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0]
s1=((X(17)-X(29))/(Q*Z),(X(18)-X(30))/(Q*Z))
t1=((X(150)-X(31))/(Q*Z),(X(151)+X(32))/(Q*Z))
pair=lambda i:(X(i),X(i+1))
at=[]
for i in (201,213,225):
 sh,th,hh=(s1,t1,pair(209)) if i==201 else (pair(i),pair(i+2),pair(i+8))
 at.append(mul(hh,add(hh,add(sh,th))))
for j,tag,part,pivot,h in [(0,'new.aggregate','new.firstTrace',605,2*X(2)-2*X(86)+26*Q+X(192)),(1,'v62.aggregate.imag','v62.firstImag',606,2*X(2)-4*X(86)+2*X(700)-8*Q+X(193))]:
 assert canonical(new[part])==canonical(Q*at[0][j]-X(pivot)),part
 assert canonical(new[tag])==canonical(h+Q*(at[1][j]+at[2][j])+X(pivot)),tag
 tested.update((part,tag))
assert tested|{'harmonic.guard','zSquared'}==set(new) and len(new)==152
# Square independently, count specialized nonzero coefficients via signed digit dominance.
qt=rd(d,'QUADRICS.json');p=rd(d,'FIXED-QUARTIC.json')
assert p['base']=={'integer':149,'exponent':{'integer':2,'exponent':763}}
from math import gcd
coeff=Counter()
for r in qt['rows']:
 ts=[(t['parameterPower'],tuple(t['monomial']),int(t['coefficient']))for t in r['terms']];assert gcd(*(v for e,m,v in ts))==1 and all(0<=e and len(m)<=2 for e,m,v in ts)
 for i,(e,m,v) in enumerate(ts):
  for j,(f,n,w) in enumerate(ts[i:],i):coeff[e+f,tuple(sorted(m+n))]+=v*w*(2 if i!=j else 1)
co={k:v for k,v in coeff.items()if v}
assert co=={(e,tuple(m)):int(v)for m,ds in p['terms']for e,v in ds} and co[0,(1,)*4]==1
assert all(e==0 for e,m in co if m==(1,)*4) and len({m for e,m in co})==len(p['terms'])
assert set().union(*(set(m)for _,m in co))==set(range(1,181))
assert max(abs(v).bit_length()for v in co.values())<1024
print(f'{len(keep)} same exact unscaled core incl signed marks, 18 harmonic equations + 5 poles + 4 aggregate parts + 2 guards. {len(co)} nonzero radix digits over {len(p["terms"])} nonzero coefficient supports; input^4=1.')
