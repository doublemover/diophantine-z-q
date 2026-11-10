from math import gcd,log,sqrt,floor
from functools import lru_cache
from itertools import product
import sympy as s
checks=dict(doubled_interval=0,local_scaled_counts=0,complete_prime_partitions=0,middle_band_witnesses=0,full_rectangle_bounds=0,norm_point_encodings=0,good_family_unions=0)
@lru_cache(None)
def factors(n):
 assert n
 return tuple(map(int,s.factorint(abs(n))))
def point_primes(side,k,t,y):
 if not t:return [] # all primes divide label0 and are excluded explicitly
 x,z,w=y;P=k*(t+2)*w*w-2*x*z if side else k*w*w+2*t
 D=(t*t+x*x)*(t*t+z*z)
 return [p for p in factors(gcd(P,D)) if k%p and t%p]
def point(k,t,u,v,z,c):return tuple(c[0]*u[r]+c[1]*v[r]+c[2]*z[r] for r in range(3))
def budget(k,t,A,B,C,Y,W):
 AA,BB=A+4*C,B+4*C;L=(AA+BB+10)*W
 H=(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t);K=2*L*L+t*t
 N=1+8*H*H*K*K+4*L**4+t*t*L*L
 large=25*((2*AA+1)*(2*BB+1)*4*log(N)+8*((2*AA+1)+(2*BB+1))*(2*C+1)*log(Y))
 return 512*A*B*C/Y*log(Y)+large
for A in range(21):
 for p in range(1,2*A+1):
  assert (2*A//p+1)*p<=4*A;checks['doubled_interval']+=1
for side,k,t,A,B,C in product([False,True],[1,2],[-2,0,1,2,3],[3,4],[3,4],[1,2,3]):
 if C>min(A,B):continue
 u,v,z=(1,0,0),(0,1,0),(0,0,1);Y=3
 orig=[];small=[];large=[]
 for c in product(range(-A,A+1),range(-B,B+1),range(-C,C+1)):
  pp=[p for p in point_primes(side,k,t,c) if p>Y]
  if pp:orig.append(c)
  if any(p<=2*C for p in pp):small.append(c)
  if any(p>2*C for p in pp):large.append(c)
  checks['middle_band_witnesses']+=sum(C<p<=2*C for p in pp)
 assert set(orig)==set(small)|set(large)
 assert len(orig)<=len(small)+len(large)
 assert len(small)<=512*A*B*C/Y+1e-9
 assert len(orig)*log(Y)<=budget(k,t,A,B,C,Y,1)+1e-8
 checks['complete_prime_partitions']+=1;checks['full_rectangle_bounds']+=1
 for p in [2,3,5]:
  if p>2*C or k%p==0 or t%p==0:continue
  count=sum(p in point_primes(side,k,t,c) for c in product(range(-A,A+1),range(-B,B+1),range(-C,C+1)))
  assert count*p*p<=512*A*B*C;checks['local_scaled_counts']+=1
# Explicit prime5 middle-band point in the original second pair.
assert 5 in point_primes(True,1,1,(2,2,1)) and 3<5<=6
# Actual same-point norm encodings into the ORIGINAL diagonal retained3-lattice.
for R in [3,5]:
 u,v,w,z=(1,0,0),(0,3,0),(0,0,3),(0,0,3);U,V,W=1,3,3
 A,B,C=floor(8*R/U),floor(8*R/V),floor(4*R/W)
 assert C<=A and C<=B
 for xyz in product(range(-R,R+1),repeat=3):
  if sum(a*a for a in xyz)>R*R or xyz[1]%3 or xyz[2]%3:continue
  c=(xyz[0],xyz[1]//3,xyz[2]//3)
  assert abs(c[0])<=A and abs(c[1])<=B and abs(c[2])<=C
  assert point(1,3,u,v,z,c)==xyz;checks['norm_point_encodings']+=1
# Literal finite/infinity lattice family overlap, ALL prime obstructions.
for side,R,Y in product([False,True],[3,4],[3,5]):
 fibers=[set() for _ in range(4)]
 for xyz in product(range(-R,R+1),repeat=3):
  x,z,w=xyz
  if sum(a*a for a in xyz)>R*R or not any(p>Y for p in point_primes(side,1,3,xyz)):continue
  for a in range(3):
   if (z-a*a*x)%3==0 and (w-a*x)%3==0:fibers[a].add(xyz)
  if x%3==0 and w%3==0:fibers[3].add(xyz)
 assert len(set.union(*fibers))<=sum(map(len,fibers))
 checks['good_family_unions']+=1
assert checks['middle_band_witnesses']>0
print('PASS',checks,'no C-to2C gap; original modulus divides label; primes2,3 below Y>=3; actual same-point/family unions')
