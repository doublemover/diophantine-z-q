#!/usr/bin/env python3
from collections import defaultdict
from itertools import product
import math,json

def prime(n):return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
N=100;gam=(0,-1,2);ps=[p for p in range(80,N) if prime(p)];P=math.prod(ps)
reps=defaultdict(list)
for c,d in product(range(-15,16),repeat=2):reps[c*c+d*d].append((c,d))
S=[]
for a,b in product(range(-15,16),repeat=2):
 u=a*a+b*b
 for w in range(1,11):
  if u-w*w not in reps:continue
  c,d=reps[u-w*w][0]
  assert a*a+b*b-c*c-d*d-w*w==0
  forms=[u+g*w*w for g in gam];key=math.prod(abs(n) for n in forms)
  weight=math.prod(math.log(max(1,abs(n))) for n in forms)
  hp=all(n>=N and prime(n) for n in forms)
  if hp:
   assert math.gcd(P,key)==1
   assert abs(weight-math.prod(math.log(n) for n in forms))<1e-10
  S.append((hp,key,weight))
prime_sum=sum(w for h,n,w in S if h);sifted=sum(w for h,n,w in S if math.gcd(P,n)==1)
assert prime_sum>0 and prime_sum<=sifted+1e-8
print(json.dumps({'actual_original_source_points':len(S),'actual_positive_prime_points':sum(h for h,n,w in S),'cutoff_primes':ps,'positive_prime_sum_dominated':True},sort_keys=True))
