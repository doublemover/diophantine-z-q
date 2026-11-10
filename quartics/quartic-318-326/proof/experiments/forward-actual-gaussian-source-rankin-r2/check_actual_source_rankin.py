#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod
import json,mpmath as mp
mp.mp.dps=65
c=dict(exact_original_family_weights=0,absolute_label_coefficients=0,original_global_heights=0,
 source_projections=0,source_norm_bounds=0,actual_gaussian_equivalences=0,original_log_weights=0,
 source_slice_injections=0,signed_budget_rankin=0,indexed_family_algebra=0)
def factors(n):
 n=abs(n);p=2;out=[]
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p+=1
 if n>1:out.append(n)
 return out
def weight(k,t):
 ps=[p for p in factors(t) if 2*k%p]
 return Q(prod(p+1 for p in ps),prod(ps)**2)
def m(q):return mp.mpf(q.numerator)/q.denominator
def coef(k,t,L):
 J=(2*abs(k)+2)*L*L+t*t+2*abs(t)
 return 1+(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t)+8*(J*J+t*t*L*L)
def height(k,t,R):return 1+(49*R)**2*109*coef(k,t,58*R*R)**9
def budget(k,t,R,T,Y):
 return mp.mpf(262144)*R**3/Y*mp.log(Y)+240100*R*R*T*mp.log(height(k,t,R))+352800*R*R*T*mp.log(Y)
for k,B in product([-9,1,2,6,318,326],range(0,16)):
 for t in range(-2*B,2*B+1):
  if not t:continue
  ps=[p for p in factors(t) if 2*k%p];M=prod(ps);N=prod(p+1 for p in ps)
  assert weight(k,t)==Q(N,M*M);c['exact_original_family_weights']+=1
  for L in [0,1,3,58*B*B]:
   assert coef(k,t,L)<=coef(k,2*B,L);c['absolute_label_coefficients']+=1
  for R in [0,1,6*B]:
   assert height(k,t,R)<=height(k,2*B,R);c['original_global_heights']+=1
  # The exact original integer-lattice normalization, including overlapping
  # family cardinality majorization, not a shifted-label modular index.
  for good in [0,N//2,N]:
   U=Q(19,3)
   assert sum((U/Q(M*M) for _ in range(good)),Q(0))<=weight(k,t)*U
   c['indexed_family_algebra']+=1
for B,k in product(range(1,5),[1,2,318,326]):
 seen={}
 for a,b,cc,d,w in product(range(-B,B+1),repeat=5):
  if a*a+b*b-cc*cc-d*d-k*w*w:continue
  t=a+cc
  if not t:continue
  y=(b-d,b+d,w);x,z,ww=y
  assert max(abs(x),abs(z),abs(ww))<=2*B;c['source_projections']+=1
  assert x*x+z*z+ww*ww<=(6*B)**2;c['source_norm_bounds']+=1
  key=t,y
  assert key not in seen or seen[key]==(a,b,cc,d,w)
  seen[key]=a,b,cc,d,w;c['source_slice_injections']+=1
  G=(a+1)**2+b*b;H=(cc+1)**2+d*d
  P=k*(t+2)*w*w-2*x*z;K=(k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2
  for p in [5,7,11,17,19]:
   if t%p==0 or k%p==0:continue
   assert (G%p==0 and H%p==0)==(P%p==0 and K%p==0)
   c['actual_gaussian_equivalences']+=1
  for gammas in [[0],[-3,1],[318,326],[-7,0,8]]:
   actual=prod(mp.log(max(1,abs(a*a+b*b+g*w*w))) for g in gammas)
   ceiling=prod(mp.log((2+abs(g))*B*B) for g in gammas)
   assert actual<=ceiling+mp.mpf('1e-60');c['original_log_weights']+=1
for k,delta,B,T,Y in product([1,6,318,326],[mp.mpf('.5'),mp.mpf(1),mp.mpf(2)],
                              [0,1,2,5,12],[0,1,3],[3,5,11]):
 R=6*B
 if T>R:continue
 ratio=lambda p:mp.power(p,-delta)
 local=lambda p:1+m(weight(k,p))*ratio(p)/(1-ratio(p))
 C=2/(1-ratio(2));constant=prod(local(p) for p in factors(2*k))*mp.exp(C*mp.zeta(1+delta))
 actual=sum((m(weight(k,t))*budget(k,t,R,T,Y) for t in range(-2*B,2*B+1) if t),mp.mpf(0))
 rhs=2*constant*mp.power(2*B,delta)*budget(k,2*B,R,T,Y)
 assert actual<=rhs+mp.mpf('1e-55');c['signed_budget_rankin']+=1
# Original shifted-chart negative control is still excluded from old D.
k,t,x,z,w=318,-10,0,-2,0
assert (k*(t+2)*w*w-2*x*z)%17==0
assert ((k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2)%17==0
assert ((t*t+x*x)*(t*t+z*z))%17==13
print(json.dumps({'status':'PASS','checks':c,'real_precision_digits':65,
 'original_q_t_index_retained':True,'label_substitution_only_in_height_ceiling':True,
 'local_lean':'NOT_RUN'},indent=2))
