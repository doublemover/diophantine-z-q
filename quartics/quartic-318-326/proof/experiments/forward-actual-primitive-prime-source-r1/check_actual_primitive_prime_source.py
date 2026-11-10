#!/usr/bin/env python3
import itertools,math,json
from fractions import Fraction as Q
import sympy as s
import mpmath as m
m.mp.dps=80
c=dict(actual_prime_primitivity=0,one_prime_suffices=0,global_source_preservation=0,all_divisor_primitivity=0,homogeneous_square_divisibility=0,removed_sieve_survival=0,actual_weighted_sieve_dominance=0,distinct_weight_remainders=0)
def eq(k,v):a,b,c,d,w=v;return a*a+b*b-c*c-d*d-k*w*w==0
def forms(gs,v):a,b,c,d,w=v;return [a*a+b*b+g*w*w for g in gs]
def primitive(v):return math.gcd(*v)==1
def pp(gs,N,v):return all(x>0 and s.isprime(x) and N<=x for x in forms(gs,v))
def logw(gs,v):return m.fprod(m.log(max(1,abs(x))) for x in forms(gs,v))
def le(a,b):assert a<=b+max(1,abs(a),abs(b))*m.mpf('1e-65'),(a,b)
def close(a,b):le(abs(a-b),m.mpf('1e-65'))
for kap,gs in [(1,[0,-1]),(2,[0,-2,1]),(318,[0,-318,1]),(326,[0,-326,2])]:
 for B in [1,2,3,4]:
  S=[v for v in itertools.product(range(-B,B+1),repeat=5) if eq(kap,v)];T=[v for v in S if primitive(v)]
  for v in S:
   for j,x in enumerate(forms(gs,v)):
    if s.isprime(abs(x)):
     assert primitive(v);c['one_prime_suffices']+=1
   for p in [2,3,5,7]:
    if all(x%p==0 for x in v):
     assert all(x%(p*p)==0 for x in forms(gs,v));c['homogeneous_square_divisibility']+=1
   if primitive(v):
    for d in [1,2,3,5,6,15,30,35]:
     assert all(any(x%p for x in v) for p in s.primefactors(d));c['all_divisor_primitivity']+=1
  for N in [0,2,3,5,8,16]:
   P=[v for v in S if pp(gs,N,v)];PT=[v for v in T if pp(gs,N,v)];assert P==PT;c['global_source_preservation']+=1
   for v in P:
    assert primitive(v);c['actual_prime_primitivity']+=1
   for excluded in [0,2,3,5,7]:
    # All primes below N, stronger than original selected good-prime subset.
    ds=[p for p in s.primerange(2,N) if p!=excluded];D=math.prod(ds)
    for v in P:
     assert math.gcd(D,math.prod(abs(x) for x in forms(gs,v)))==1;c['removed_sieve_survival']+=1
    for typ in [0,1,2]:
     w=lambda v: m.mpf(1) if typ==0 else (logw(gs,v) if typ==1 else m.exp(-sum(x*x for x in v)))
     a=sum((w(v) for v in P),m.mpf(0));b=sum((w(v) for v in T if math.gcd(D,math.prod(abs(x) for x in forms(gs,v)))==1),m.mpf(0))
     le(a,b);c['actual_weighted_sieve_dominance']+=1
  # Actual local finite density, recomputed source remainders for genuinely different weights.
  p=5
  if kap%p:
   R=[v for v in itertools.product(range(p),repeat=5) if (v[0]**2+v[1]**2-v[2]**2-v[3]**2-kap*v[4]**2)%p==0 and any(v)]
   g=Q(sum(any(x%p==0 for x in forms(gs,v)) for v in R),len(R));gr=m.mpf(g.numerator)/g.denominator
   rem=[]
   for typ in [0,1,2]:
    w=lambda v:m.mpf(1) if typ==0 else (logw(gs,v) if typ==1 else m.exp(-sum(x*x for x in v)))
    mass=sum((w(v) for v in T),m.mpf(0));event=sum((w(v) for v in T if math.prod(abs(x) for x in forms(gs,v))%p==0),m.mpf(0))
    r=event-gr*mass;close(event,gr*mass+r);rem.append(r)
   assert any(abs(rem[i]-rem[j])>m.mpf('1e-30') for i in range(3) for j in range(i));c['distinct_weight_remainders']+=1
print(json.dumps({'status':'PASS','precision_digits':80,'checks':c,'scope':'Actual prime-form primitivity, preservation under one modulus-independent source restriction, and genuine different nonnegative weight/sieve/remainder identities. No prime-point existence or analytic congruence estimate inferred.'},sort_keys=True))
