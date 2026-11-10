#!/usr/bin/env python3
from fractions import Fraction as Q
from math import gcd, prod
import json
import mpmath as mp
mp.mp.dps=65

def factors(n):
 n=abs(n);p=2;out=[]
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p+=1
 if n>1:out.append(n)
 return out

def weight(k,n):
 if n==0:return Q(0)
 return prod((Q(1) if 2*k%p==0 else Q(p+1,p*p)) for p in factors(n))
def literal(k,t):
 ps=[p for p in factors(t) if 2*k%p]
 return Q(prod(p+1 for p in ps),prod(ps)**2)
def prime(p):return p>=2 and factors(p)==[p] and all(p%d for d in range(2,int(p**.5)+1))
def m(q):return mp.mpf(q.numerator)/q.denominator
c=dict(final_index_weight=0,coprime=0,prime_powers=0,excluded_powers=0,finite_rankin=0,local_excess=0,uniform_euler=0,signed_labels=0)
for k in [-9,-3,-1,0,1,2,6,30]:
 for n in range(1,301):
  assert weight(k,n)==literal(k,n)==literal(k,-n);c['final_index_weight']+=1
 for a in range(1,50):
  for b in range(1,40):
   if gcd(a,b)==1:assert weight(k,a*b)==weight(k,a)*weight(k,b);c['coprime']+=1
 for p in [2,3,5,7,11,13]:
  for e in range(1,7):
   assert weight(k,p**e)==weight(k,p);c['prime_powers']+=1
   if 2*k%p==0:assert weight(k,p**e)==1;c['excluded_powers']+=1
for k in [-9,-3,-1,1,2,6,30]:
 for delta in [mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf(1),mp.mpf(2)]:
  ratio=lambda p:mp.power(p,-delta)
  local=lambda p:1+m(weight(k,p))*ratio(p)/(1-ratio(p))
  C=2/(1-ratio(2));bad=prod(local(p) for p in factors(2*k))
  constant=bad*mp.exp(C*mp.zeta(1+delta))
  for p in range(2,101):
   if prime(p) and 2*k%p:
    assert local(p)<=1+C*mp.power(p,-1-delta);c['local_excess']+=1
  for B in [0,1,2,3,7,12,25,50,100]:
   exact=sum((weight(k,n) for n in range(1,B+1)),Q(0))
   lp=prod(local(p) for p in range(2,B+1) if prime(p))
   assert m(exact)<=mp.power(B,delta)*lp+mp.mpf('1e-60');c['finite_rankin']+=1
   assert lp<=constant;c['uniform_euler']+=1
   signed=sum((literal(k,t) for t in range(-2*B,2*B+1) if t),Q(0))
   positive=sum((weight(k,n) for n in range(1,2*B+1)),Q(0))
   assert signed==2*positive
   assert m(signed)<=2*constant*mp.power(2*B,delta)+mp.mpf('1e-60');c['signed_labels']+=1
# Negative control: dropping excluded-prime powers changes the exact original coefficient.
assert weight(6,2**8*3**5)==1
assert Q(3,4)*Q(4,9)!=weight(6,2**8*3**5)
# Exact local geometric partial sums are strictly bounded by the claimed full series.
for k in [1,6,-3]:
 for p in [2,3,5,7]:
  for d in [1,2,3]:
   r=Q(1,p**d);w=weight(k,p)
   for N in [0,1,2,10]:
    partial=1+w*sum((r**e for e in range(1,N+1)),Q(0))
    full=1+w*r/(1-r)
    assert full-partial==w*r**(N+1)/(1-r)
print(json.dumps({'status':'PASS','checks':c,'exact_local_geometric_checks':144,'real_inequality_precision_digits':65,'note':'Finite exact/numerical regression checks only; no Lean execution or replacement for proof.'},indent=2))
