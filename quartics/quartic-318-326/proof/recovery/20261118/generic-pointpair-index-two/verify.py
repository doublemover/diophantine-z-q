"""Elementary low-degree consistency controls; theorem itself is symbolic in README."""
from fractions import Fraction as F
import json
from itertools import product
# Over characteristic zero rational maps to a quadratic pair have a
# partition of the degree over each geometric target; enumerate possibilities.
def parts(n,lower=1):
 if n==0:yield ()
 for a in range(lower,n+1):
  for z in parts(n-a,a):yield (a,)+z
cnt=0
for m in range(1,14):
 for P,Q in product(parts(m),repeat=2):
  a=sum(z%2 for z in P);b=sum(z%2 for z in Q)
  assert 2*a%4==2*m%4 and (2*a+2*b)%4==0
  cnt+=1
pairtests=0
for beta in (5,17,187,204618888056724185):
 for u in (F(1,3),F(4,9),F(18,5)):
  e=F(1-beta,1+3*beta); B=beta*u*u; y=4*beta*beta*u**3/(1+3*beta)
  assert y and y*y==B*(B-B*e)*(B+3*B*e)
  # Replace V by S², as in the quadratic extension identity.
  S=F(3,2);V=S*S
  assert (S**3*y)**2==B*S**2*(B*S**2-B*e*V)*(B*S**2+3*B*e*V)
  pairtests+=1
print(json.dumps(dict(local_degree_partition_pairs=cnt,explicit_seed_cubic_checks=pairtests),indent=2))
