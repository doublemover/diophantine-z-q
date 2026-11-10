#!/usr/bin/env python3
from itertools import product
from collections import Counter
from fractions import Fraction as Q
import sympy as s,mpmath as mp,json
mp.mp.dps=70
c=dict(original_level_source_injections=0,original_value_bounds=0,
 signed_square_level_counts=0,square_scaled_counts=0,actual_prime_bound=0,
 original_p_squared_divisibility=0,both_source_level_covers=0,
 reciprocal_prime_tails=0,both_label_count_bounds=0,full_source_cover_points=0,
 full_weighted_partitions=0,fixed_coefficient_exclusion_removed=0)
def valuebudget(B,k):
 D=4 # exact constructed divisorConstant(2): eta1,q2,A2,cutoff2.
 return (2*D*(4*B*B)**2)*((4*B+1)*(2*D*(4*(abs(k)+1)*B*B)**2)+4*(4*B+1))
for N,p in product(range(0,121),[2,3,5,7,11,17]):
 vals=[v for v in range(-N,N+1) if v and v%(p*p)==0]
 image=[(v<0,abs(v)//(p*p)) for v in vals]
 assert len(image)==len(set(image))==2*(N//(p*p));c['signed_square_level_counts']+=1
 assert len(vals)*p*p<=2*N;c['square_scaled_counts']+=1
for B,k in product(range(0,6),[-3,1,2,318,326]):
 points=[];levels=Counter();enc={}
 for a,b,cc,d,w in product(range(-B,B+1),repeat=5):
  if a*a+b*b-cc*cc-d*d-k*w*w:continue
  x0,x1=a+cc,a-cc;y=b-d,b+d,w;r=k*w*w-y[0]*y[1]
  assert x0*x1==r and abs(r)<=4*B*B;c['original_value_bounds']+=1
  e=(x0,x1,y)
  assert e not in enc or enc[e]==(a,b,cc,d,w);enc[e]=(a,b,cc,d,w)
  c['original_level_source_injections']+=1
  levels[r]+=1
  G,H=(a+1)**2+b*b,(cc+1)**2+d*d
  W=mp.log(max(1,abs(a*a+b*b+w*w)))*mp.log(max(1,abs(a*a+b*b+2*w*w)))
  points.append(((a,b,cc,d,w),x0,x1,r,G,H,W))
 for r,n in levels.items():
  if r:assert n<=valuebudget(B,k)
 for Y in [1,3,5,max(3,abs(k))]:
  ps=list(s.primerange(Y+1,2*B+1))
  rs=sum((Q(1,p*p) for p in ps),Q(0))
  assert rs<=Q(1,Y);c['reciprocal_prime_tails']+=1
  both=[];images=[]
  for pt,x0,x1,r,G,H,W in points:
   candidates=[p for p in ps if x0%p==0 and x1%p==0]
   if not r or not candidates:continue
   p=candidates[0]
   assert p<=2*B;c['actual_prime_bound']+=1
   assert r%(p*p)==0;c['original_p_squared_divisibility']+=1
   assert 0<abs(r)<=4*B*B
   images.append((p,r,pt));both.append(pt);c['both_source_level_covers']+=1
  assert len(images)==len(set(images))
  assert len(both)<=Q(8*B*B,Y)*valuebudget(B,k);c['both_label_count_bounds']+=1
  primes=list(s.primerange(Y+1,max(Y+20,2*(B+1)**2+20)))
  fullmass=mp.mpf(0);zeromass=mp.mpf(0);bothmass=mp.mpf(0);chartmass=mp.mpf(0);cover=[]
  for pt,x0,x1,r,G,H,W in points:
   if not r:zeromass+=W
   if pt in both:bothmass+=W
   eligible=[p for p in primes if k%p and G%p==0 and H%p==0]
   if x1 and any(x1%p for p in eligible):chartmass+=W
   if x0 and any(x0%p for p in eligible):chartmass+=W
   if not eligible:continue
   fullmass+=W;p=eligible[0]
   if not r:key='zero',pt
   elif x0%p==0 and x1%p==0:
    assert pt in both
    key='both',pt
   else:
    side=False if x0%p==0 else True;t=x0 if side else x1
    assert t and t%p and abs(t)<=2*B
    key='chart',side,t,pt
   cover.append(key);c['full_source_cover_points']+=1
  assert len(cover)==len(set(cover))
  assert fullmass<=zeromass+bothmass+chartmass+mp.mpf('1e-55')
  c['full_weighted_partitions']+=1
  if Y>=abs(k):
   for pt,x0,x1,r,G,H,W in points:
    allps=[p for p in primes if G%p==0 and H%p==0]
    assert all(k%p for p in allps);c['fixed_coefficient_exclusion_removed']+=1
print(json.dumps({'status':'PASS','checks':c,'real_precision_digits':70,
 'all_original_source_strata_covered':True,'coefficient_exception_removed_for_Y_ge_abs_kappa':True,
 'prime_existence_claimed':False,'local_lean':'NOT_RUN'},indent=2))
