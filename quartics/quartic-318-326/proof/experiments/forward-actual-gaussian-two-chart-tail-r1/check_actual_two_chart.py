#!/usr/bin/env python3
from itertools import product
from fractions import Fraction as Q
from math import prod
import json,mpmath as mp
mp.mp.dps=65
c=dict(first_label_height=0,first_gaussian_bridge=0,actual_original_lattice_covers=0,
 fixed_source_injections=0,overlap_weighted_partitions=0,weighted_partition_points=0,
 two_chart_tail_algebra=0)
def factors(n):
 n=abs(n);p=2;out=[]
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p+=1
 if n>1:out.append(n)
 return out
def fh(k,t,L):
 F=(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t);N=2*L*L+t*t
 return 1+8*F*F*N*N+4*L**4+t*t*L*L
for k,B,R in product([-7,1,318,326],range(0,15),[0,1,6,24]):
 for t in range(-2*B,2*B+1):
  assert fh(k,t,58*R*R)<=fh(k,2*B,58*R*R);c['first_label_height']+=1
for B,k,side in product(range(1,5),[1,2,318,326],[False,True]):
 groups={}
 for a,b,cc,d,w in product(range(-B,B+1),repeat=5):
  if a*a+b*b-cc*cc-d*d-k*w*w:continue
  t=a+cc if side else a-cc
  if not t:continue
  x,z=b-d,b+d;y=x,z,w
  G,H=(a+1)**2+b*b,(cc+1)**2+d*d
  P=k*w*w+2*t;Pp=k*(t+2)*w*w-2*x*z
  K=(k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2;D=(t*t+x*x)*(t*t+z*z)
  obstruction=False
  for p in [5,7,11,17,19]:
   if t%p==0 or k%p==0:continue
   actual=G%p==0 and H%p==0
   if not side:
    assert actual==(P%p==0 and K%p==0)==(P%p==0 and D%p==0)
    c['first_gaussian_bridge']+=1
   obstruction|=actual
  ps=[p for p in factors(t) if 2*k%p]
  witnesses=[]
  for ss in product(*[[None]+list(range(p)) for p in ps]):
   if all((x%p==0 and w%p==0) if s is None else
          ((z-k*s*s*x)%p==0 and (w-s*x)%p==0) for p,s in zip(ps,ss)):
    witnesses.append(ss)
  assert witnesses;c['actual_original_lattice_covers']+=1
  assert (k*w*w-x*z)%prod(ps)==0
  original=(a,b,cc,d,w);key=t,y
  data=groups.setdefault(t,{})
  assert y not in data or data[y][0]==original;c['fixed_source_injections']+=1
  wt=prod(mp.log(max(1,abs(a*a+b*b+g*w*w))) for g in [-3,1,318,326])
  data[y]=original,witnesses,obstruction,wt
 # Since source_cover is valid for ANY good/bad predicate on the actual
 # original lattice family, test distinct overlapping witness partitions.
 for t,data in groups.items():
  for partition in range(4):
   bad=lambda ss: (sum(0 if s is None else s+1 for s in ss)+partition)%3==0
   src=sum((v[3] for v in data.values() if v[2]),mp.mpf(0))
   good=sum((v[3] for v in data.values() if v[2] and any(not bad(s) for s in v[1])),mp.mpf(0))
   badmass=sum((v[3] for v in data.values() if any(bad(s) for s in v[1])),mp.mpf(0))
   images=set()
   for y,v in data.items():
    if not v[2]:continue
    chosen=v[1][0];image=bad(chosen),v[0]
    assert image not in images;images.add(image);c['weighted_partition_points']+=1
   assert src<=good+badmass+mp.mpf('1e-55');c['overlap_weighted_partitions']+=1
# Exact final two-chart inequality algebra, including zero weights.
for T,Y,W,K,V0,V1,A in product([Q(1,2),Q(1),Q(3)],[3,5],[0,1,7],[1,3],[0,2],[0,5],[0,11]):
 L=mp.log(Y);t=mp.mpf(T.numerator)/T.denominator
 g0=K*V0*W/L;g1=K*V1*W/L;b=A*W/t**3
 lhs=(g0+g1+2*b)*L*t**3
 rhs=K*(V0+V1)*W*t**3+2*A*W*L
 assert abs(lhs-rhs)<mp.mpf('1e-55');c['two_chart_tail_algebra']+=1
print(json.dumps({'status':'PASS','checks':c,'real_precision_digits':65,
 'first_D_substitution_only_side_false':True,'source_cover_uses_original_q_t':True,
 'overlap_tests_arbitrary_classifiers_not_claimed_minima':True,'local_lean':'NOT_RUN'},indent=2))
