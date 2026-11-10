#!/usr/bin/env python3
import itertools,json,math
from fractions import Fraction as F
import mpmath as m
import sympy as s
m.mp.dps=90
counts=dict(exact_bernoulli_totals=0,exact_first_moments=0,markov_truncations=0,abel_identities=0,chebyshev_log_bounds=0,actual_local_densities=0,actual_density_moments=0,integer_modulus_injections=0,odds_probability_identities=0,actual_half_euler=0,polynomial_thresholds=0)
def le(a,b):assert a<=b*(1+m.mpf('1e-70'))+m.mpf('1e-70'),(a,b)
def close(a,b):assert abs(a-b)<=max(1,abs(a),abs(b))*m.mpf('1e-70'),(a,b)
def mp(q):return m.mpf(q.numerator)/q.denominator if isinstance(q,F) else m.mpf(q)
for n in range(7):
 for typ in range(4):
  q=[F((i+typ)%5,5) for i in range(n)];l=[F(i+1,typ+1) for i in range(n)]
  ff=list(itertools.product([False,True],repeat=n))
  prob=lambda f:math.prod(q[i] if f[i] else 1-q[i] for i in range(n))
  cost=lambda f:sum(l[i] for i in range(n) if f[i])
  assert sum(prob(f) for f in ff)==1;counts['exact_bernoulli_totals']+=1
  M=sum(q[i]*l[i] for i in range(n))
  assert sum(prob(f)*cost(f) for f in ff)==M;counts['exact_first_moments']+=1
  for L in [F(1,10),F(1),F(3),2*M+1]:
   short=sum(prob(f) for f in ff if cost(f)<L)
   assert short>=1-M/L
   if M<=L/2:assert short>=F(1,2)
   counts['markov_truncations']+=1
for N in range(1,80):
 for typ in range(3):
  a=lambda n:F((n*n+typ*n+1)%13-3,typ+1)
  A=lambda n:sum(a(i) for i in range(1,n+1))
  lhs=sum(a(i)/i for i in range(1,N+1))
  rhs=A(N)/N+sum(A(i)*(F(1,i)-F(1,i+1)) for i in range(1,N))
  assert lhs==rhs;counts['abel_identities']+=1
for N in list(range(1,80))+[100,1000,10000]:
 ps=list(s.primerange(2,N+1));theta=sum(m.log(p) for p in ps)
 le(theta,m.log(4)*N)
 moment=sum(m.log(p)/p for p in ps)
 le(moment,m.log(4)*(1+m.log(N)));counts['chebyshev_log_bounds']+=1
 for excluded in [2,3,13,59]:
  le(sum(m.log(p)/p for p in ps if p!=excluded),m.log(4)*(1+m.log(N)));counts['chebyshev_log_bounds']+=1

def density(p,k):
 chi=1 if p%4==1 else -1
 v0=p+(p-1)*chi
 return F((p-1)*(p-chi)*(2*v0+(k-2)*(p-chi))+v0*v0-1,p**4-1)
for k in range(2,9):
 for p in s.primerange(16*(k+2),1000):
  q=density(p,k);assert 0<q<=F(1,2) and q<=F(5*k+6,p)
  counts['actual_local_densities']+=1
for kappa,gs,N in [(1,[0,-1],80),(318,[0,-318,1],105),(326,[0,-326,1],105),(3,[0,-3,2,5],125)]:
 k=len(gs);exception=2*abs(kappa)*math.prod(abs(gs[i]-gs[j]) for i in range(k) for j in range(i+1,k))
 selected=[p for p in s.primerange(16*(k+2),N) if exception%p]
 for excluded in [0,2]+selected[:2]:
  ps=[p for p in selected if p!=excluded];q=[density(p,k) for p in ps];ff=list(itertools.product([False,True],repeat=len(ps)))
  M=sum(mp(qi)*m.log(p) for p,qi in zip(ps,q));bound=(5*k+6)*m.log(4)*(1+m.log(N))
  le(M,bound);counts['actual_density_moments']+=1
  modulus=lambda f:math.prod(p for p,b in zip(ps,f) if b)
  ds=[modulus(f) for f in ff];assert len(set(ds))==len(ds)
  full=math.prod(ps)
  for f,d in zip(ff,ds):
   assert d>0 and full%d==0
   assert all((d%p==0)==b for p,b in zip(ps,f))
   close(m.log(d),sum(m.log(p) for p,b in zip(ps,f) if b));counts['integer_modulus_injections']+=1
  E=math.prod(F(1)/(1-qi) for qi in q)
  odds=lambda f:math.prod(qi/(1-qi) if b else F(1) for qi,b in zip(q,f))
  prob=lambda f:math.prod(qi if b else 1-qi for qi,b in zip(q,f))
  for f in ff:
   assert E*prob(f)==odds(f);counts['odds_probability_identities']+=1
  assert sum(odds(f) for f in ff)==E
  for L in [1+2*M,1+2*bound]:
   z=m.exp(L)
   trunc=sum(mp(odds(f)) for f in ff if modulus(f)<z)
   le(mp(E)/2,trunc);counts['actual_half_euler']+=1
  close(m.exp(1+2*bound),m.exp(1+2*(5*k+6)*m.log(4))*m.mpf(N)**(2*(5*k+6)*m.log(4)))
  counts['polynomial_thresholds']+=1
print(json.dumps({'status':'PASS','precision_digits':90,'checks':counts,'scope':'Exact finite Bernoulli/Abel identities, actual local densities and distinct integer divisor truncation; no Mertens denominator asymptotic or integer-point remainder asserted.'},sort_keys=True))
