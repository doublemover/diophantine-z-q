from fractions import Fraction as F
from itertools import combinations
from math import prod
from verify import beta,primes,e
p=13
assert (pow(7,-1,p)*(-3))%p==7 and pow(7,6,p)==12
assert beta%8==1 and -3%8==5
K=312*beta;options=[]
for k in range(11):
 for subset in combinations([3,13]+primes,k):
  for even in (2,4):
   a=even*prod(subset); b=K//a
   options.append((max(a/e,b/(2+e)),a,b))
bound,a,b=min(options)
assert len(options)==2048 and (a,b)==(19830,3219419721316084)
assert bound>1609709860647970
print('exact allocation floor >',1609709860647970)
