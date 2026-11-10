from fractions import Fraction as Q
from itertools import product
from pathlib import Path
checks={'telescoping_prefix':0,'finite_reciprocal_sets':0,'scaled_prime_fibers':0,'finite_union_tails':0,'overlap_unions':0,'rectangle_volumes':0}
for Y in range(1,31):
 for K in range(41):
  s=sum((Q(1,(Y+i+1)**2) for i in range(K)),Q(0))
  assert s<=Q(1,Y)-Q(1,Y+K)
  checks['telescoping_prefix']+=1
 for step in range(1,8):
  S=list(range(Y+1,Y+80,step))
  assert sum((Q(1,p*p) for p in S),Q(0))<=Q(1,Y)
  checks['finite_reciprocal_sets']+=1
for A,B,C in [(4,5,7),(7,9,11),(3,3,3)]:
 for t in [1,-2,3]:
  for shear in [0,1,2]:
   coords=list(product(range(-A,A+1),range(-B,B+1),range(-C,C+1)))
   for Y in [1,2,3]:
    S=[p for p in [2,3,5,7,11] if Y<p<=min(A,B,C) and t%p]
    for side in [False,True]:
     def obstruction(c,p):
      a,b,d=c;x=a+shear*b;z=b+shear*d;w=d
      P=(t+2)*w*w-2*x*z if side else w*w+2*t
      D=(t*t+x*x)*(t*t+z*z)
      return P%p==0 and D%p==0
     sets=[{c for c in coords if obstruction(c,p)} for p in S]
     for p,ss in zip(S,sets):
      assert len(ss)*p*p<=216*A*B*C
      checks['scaled_prime_fibers']+=1
     union=set().union(*sets)
     assert len(union)<=sum(map(len,sets))
     assert Q(len(union))<=Q(216*A*B*C,Y)
     checks['finite_union_tails']+=1
     if len(union)<sum(map(len,sets)):checks['overlap_unions']+=1
# p must fit every side: A=C=0,B=1,t=1,p=2 gives an actual obstruction butABC=0.
x,z,w=0,1,0;p=2;t=1
assert (w*w+2*t)%p==0 and ((t*t+x*x)*(t*t+z*z))%p==0
for U,V,W in [(1,1,1),(1,2,3),(2,3,5),(Q(3,2),Q(5,2),Q(7,2))]:
 for R in map(Q,range(15)):
  A=int(8*R/U);B=int(8*R/V);C=int(4*R/W)
  for numerator in range(1,21):
   det=Q(numerator,10)*U*V*W
   assert A*B*C*det<=512*R**3
   checks['rectangle_volumes']+=1
for f in ['OriginalReducedRectangleVolume318','OriginalReciprocalSquareTail318' ,'OriginalFiniteSieveUnion318','OriginalSmallPrimeRectangleTail318']:
 s=(Path(__file__).parent/(f+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in s
print('PASS',checks,'negative: dropping shortest-side condition makes scaled estimate false')
