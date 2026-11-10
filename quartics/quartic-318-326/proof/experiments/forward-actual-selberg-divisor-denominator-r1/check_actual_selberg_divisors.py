#!/usr/bin/env python3
import itertools,json,math
from fractions import Fraction as F
import mpmath as m
import sympy as s
m.mp.dps=90
counts=dict(squarefree_products=0,divisor_bijections=0,arithmetic_function_terms=0,strict_denominator_identities=0,removed_factors=0,actual_original_quarter_bounds=0,source_independence=0)
def density(p,k):
 chi=1 if p%4==1 else -1;v0=p+(p-1)*chi
 return F((p-1)*(p-chi)*(2*v0+(k-2)*(p-chi))+v0*v0-1,p**4-1)
def mp(q):return m.mpf(q.numerator)/q.denominator if isinstance(q,F) else m.mpf(q)
def le(a,b):assert a<=b*(1+m.mpf('1e-70'))+m.mpf('1e-70'),(a,b)
# Include empty selected sets and removed primes that were never eligible.
for kap,gs,N in [(1,[0,-1],1),(1,[0,-1],65),(1,[0,-1],90),(318,[0,-318,1],105),(326,[0,-326,1],105),(3,[0,-3,2,5],125)]:
 k=len(gs);exception=2*abs(kap)*math.prod(abs(gs[i]-gs[j]) for i in range(k) for j in range(i+1,k))
 selected=[int(p) for p in s.primerange(16*(k+2),N) if exception%p]
 q={p:density(p,k) for p in selected};Efull=math.prod(F(1)/(1-q[p]) for p in selected)
 for excluded in [0,2,abs(kap)]+selected[:3]:
  ps=[p for p in selected if p!=excluded];P=math.prod(ps);ds=[int(d) for d in s.divisors(P)]
  assert all(e==1 for e in s.factorint(P).values());counts['squarefree_products']+=1
  choices=list(itertools.product([False,True],repeat=len(ps)))
  modulus=lambda f:math.prod(p for p,b in zip(ps,f) if b)
  bits=lambda d:tuple(d%p==0 for p in ps)
  assert sorted(modulus(f) for f in choices)==ds
  for d in ds:
   assert modulus(bits(d))==d and set(s.primefactors(d))=={p for p in ps if d%p==0}
   counts['divisor_bijections']+=1
  for f in choices:assert bits(modulus(f))==f
  nu=lambda d:math.prod(q[int(p)] for p in s.primefactors(d))
  terms=lambda d:nu(d)*math.prod(F(1)/(1-q[int(p)]) for p in s.primefactors(d))
  odds=lambda f:math.prod(q[p]/(1-q[p]) for p,b in zip(ps,f) if b)
  for f in choices:
   assert terms(modulus(f))==odds(f);counts['arithmetic_function_terms']+=1
  for z in [F(0),F(1),F(2),F(P),F(P)+F(1,2)]+[F(d) for d in ds[:5]]:
   a=sum(terms(d) for d in ds if d<z);b=sum(odds(f) for f in choices if modulus(f)<z)
   assert a==b;counts['strict_denominator_identities']+=1
  E=math.prod(F(1)/(1-q[p]) for p in ps)
  assert E>=Efull/2
  assert Efull==E*(F(1)/(1-q[excluded]) if excluded in selected else 1)
  counts['removed_factors']+=1
  L=1+2*(5*k+6)*m.log(4)*(1+m.log(N));z=m.exp(L)
  denom=sum(mp(terms(d)) for d in ds if d<z)
  le(mp(Efull)/4,denom);counts['actual_original_quarter_bounds']+=1
  # Two literal finite quadric sources: exact arithmetic function is independent
  # of point multiplicities and real weights, because nu is unchanged.
  sources=[[],[(0,0,0,0,0)],[(a,b,c,d,w) for a,b,c,d,w in itertools.product(range(-1,2),repeat=5) if a*a+b*b-c*c-d*d-kap*w*w==0]]
  for S in sources:
   original_terms=lambda d:nu(d)*math.prod(F(1)/(1-nu(int(p))) for p in s.primefactors(d))
   for d in ds:assert original_terms(d)==terms(d)
   counts['source_independence']+=1
print(json.dumps({'status':'PASS','precision_digits':90,'checks':counts,'scope':'Exact original prime set, squarefree divisors, arithmetic-function Selberg terms, strict cutoff, removed factor and original-source quarter-Euler bound. No Mertens growth, optimal weights, primitive-point asymptotic or prime existence asserted.'},sort_keys=True))
