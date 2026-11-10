#!/usr/bin/env python3
import itertools,json,math
from fractions import Fraction as F
import mpmath as m
import sympy as s
m.mp.dps=90
c=dict(boolean_matrix_inversions=0,inverse_transforms=0,normalizations=0,strict_support=0,diagonal_coordinates=0,exact_energies=0,actual_divisor_coefficients=0,actual_source_bounds=0,produced_euler_main_bounds=0)
def le(a,b):assert a<=b+max(1,abs(a),abs(b))*m.mpf('1e-70'),(a,b)
def mp(q):return m.mpf(q.numerator)/q.denominator if isinstance(q,F) else m.mpf(q)
def zeta(a,b):return int(all(not x or y for x,y in zip(a,b)))
def mu(a,b):return math.prod((int(y) if x else (-1 if y else 1)) for x,y in zip(a,b))
def sign(a):return (-1)**sum(a)
for n in range(6):
 bs=list(itertools.product([False,True],repeat=n))
 for a in bs:
  for d in bs:
   assert sum(zeta(a,b)*mu(b,d) for b in bs)==int(a==d);c['boolean_matrix_inversions']+=1
 target={b:F((i*7)%11-5,3) for i,b in enumerate(bs)}
 inv={a:sum(mu(a,b)*target[b] for b in bs) for a in bs}
 for a in bs:
  assert sum(zeta(a,b)*inv[b] for b in bs)==target[a];c['inverse_transforms']+=1

def run(ps,q,levels,actual=None):
 bs=list(itertools.product([False,True],repeat=len(ps)));zero=(False,)*len(ps)
 d={a:math.prod(p for p,b in zip(ps,a) if b) for a in bs};P=math.prod(ps)
 nu=lambda n:math.prod(q[int(p)] for p in s.primefactors(n))
 g={a:math.prod(q[p]/(1-q[p]) for p,b in zip(ps,a) if b) for a in bs}
 E=math.prod(F(1)/(1-q[p]) for p in ps)
 for z in levels:
  cut={a:d[a]<z for a in bs};L=sum(g[a] for a in bs if cut[a]);assert L>0
  target={a:sign(a)*g[a]/L if cut[a] else F(0) for a in bs}
  coeff={a:sum(mu(a,b)*target[b] for b in bs)/nu(d[a]) for a in bs}
  assert coeff[zero]==1;c['normalizations']+=1
  for a in bs:
   if not cut[a]:assert coeff[a]==0
   c['strict_support']+=1
   assert sum(nu(d[b])*coeff[b] for b in bs if d[b]%d[a]==0)==target[a]
   c['diagonal_coordinates']+=1;c['actual_divisor_coefficients']+=1
  energy=sum(target[a]**2/g[a] for a in bs)
  direct=sum(coeff[a]*coeff[b]*nu(math.lcm(d[a],d[b])) for a in bs for b in bs)
  assert energy==direct==1/L;c['exact_energies']+=1
  if actual:
   kap,gs=actual
   pts=[(a,b,cc,dd,w) for a,b,cc,dd,w in itertools.product(range(-1,2),repeat=5) if a*a+b*b-cc*cc-dd*dd-kap*w*w==0]
   values=lambda v:[v[0]**2+v[1]**2+h*v[4]**2 for h in gs]
   key=lambda v:math.prod(abs(t) for t in values(v))
   wt=lambda v:math.prod(m.log(max(1,abs(t))) for t in values(v))
   for S in [[],pts[:7],pts]:
    X=sum(wt(v) for v in S)
    lam2={r:sum(coeff[a]*coeff[b] for a in bs for b in bs if math.lcm(d[a],d[b])==r) for r in d.values()}
    remainder={r:sum(wt(v) for v in S if key(v)%r==0)-mp(nu(r))*X for r in d.values()}
    err=sum(mp(lam2[r])*remainder[r] for r in d.values())
    sift=sum(wt(v) for v in S if math.gcd(P,key(v))==1)
    le(sift,X/mp(L)+err);c['actual_source_bounds']+=1
  if z>max(d.values()):assert L==E;c['produced_euler_main_bounds']+=1
for n in range(6):
 ps=list(s.primerange(2,20))[:n];q={int(p):F(i+1,2*i+3) for i,p in enumerate(ps)};ps=list(map(int,ps));P=math.prod(ps)
 run(ps,q,[F(3,2),F(max(2,P)),F(P)+1,F(10)])
def density(p,k):
 chi=1 if p%4==1 else -1;v0=p+(p-1)*chi
 return F((p-1)*(p-chi)*(2*v0+(k-2)*(p-chi))+v0*v0-1,p**4-1)
for kap,gs,N in [(1,[0,-1],80),(318,[0,-318,1],95),(326,[0,-326,1],95)]:
 k=len(gs);exception=2*abs(kap)*math.prod(abs(gs[i]-gs[j]) for i in range(k) for j in range(i+1,k))
 selected=[int(p) for p in s.primerange(16*(k+2),N) if exception%p]
 q={p:density(p,k) for p in selected};Efull=math.prod(F(1)/(1-q[p]) for p in selected)
 for excluded in [0]+selected[:1]:
  ps=[p for p in selected if p!=excluded];P=math.prod(ps)
  z=m.exp(1+2*(5*k+6)*m.log(4)*(1+m.log(N)))
  run(ps,q,[F(3,2),F(ps[0]) if ps else F(2),z],(kap,gs))
  E=math.prod(F(1)/(1-q[p]) for p in ps);assert 1/E<=4/Efull
print(json.dumps({'status':'PASS','precision_digits':90,'checks':c,'scope':'Constructed finite Mobius coefficients, exact standard main-sum energy, strict natural-modulus support and actual original weighted-source inequality. Error stays exact; no distribution asymptotic assumed.'},sort_keys=True))
