from itertools import product
from math import gcd
import json
c=dict(finite_factor_levels=0,stabilized_levels=0,free_finite_formulas=0,transition_kernels=0,rational_scalar_squares=0)
for ns in [(1,),(2,),(4,),(8,),(3,),(12,),(2,6),(4,12),(8,24)]:
 G=list(product(*(range(n) for n in ns)));cards=[]
 for k in range(12):
  m=2**k
  ker={x for x in G if all(m*a%n==0 for a,n in zip(x,ns))}
  image={tuple(m*a%n for a,n in zip(x,ns)) for x in G}
  assert len(G)//len(image)==len(ker)
  cards.append(len(ker));c['finite_factor_levels']+=1
  for r in range(3):
   assert m**r*len(G)//len(image)==m**r*len(ker);c['free_finite_formulas']+=1
 assert all(a<=b for a,b in zip(cards,cards[1:]))
 for k in range(6,12):assert cards[k]==cards[6];c['stabilized_levels']+=1
for j in range(1,8):
 N=2**j
 for a in range(N):
  if a*a%N!=1:continue
  for k in range(j):
   m=2**k
   ZT={z for z in range(N) if (a+1)*z%N==0 and m*z%N==0}
   Bnext={(a-1)*q%N for q in range(N) if 2*m*q%N==0}
   connect={((a-1)*q)%N for q in range(N) if 2*m*q%N==0 and (a-1)*m*q%N==0}
   assert ZT&Bnext==connect;c['transition_kernels']+=1
   for q in range(N):
    P=m*q%N
    if (a-1)*P%N:continue
    assert 2*m*q%N==2*P%N
    assert (a+1)*(a-1)*q%N==0
    c['rational_scalar_squares']+=1
print(json.dumps({'status':'PASS','counts':c},indent=2))
