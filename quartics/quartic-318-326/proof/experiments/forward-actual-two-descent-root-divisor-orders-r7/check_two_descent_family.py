#!/usr/bin/env python3
"""Independent finite exact regressions, not a Lean build or proof substitute."""
import json, math
from pathlib import Path
from sympy import primerange, legendre_symbol, factorint
PRIMES=list(primerange(3,300000))
checks={'families':0,'symbol_entries':0,'reciprocity_entries':0,'twist_domains':0}
def char(a,p):
 r=pow(a%p,(p-1)//2,p)
 return -1 if r==p-1 else r

def family(seed,k,special,bits,N,forbidden):
 out=[]
 for i in range(k):
  support=seed+out
  targets=[-1 if bits(i,j) else 1 for j in range(len(support))]
  q=next(q for q in PRIMES if q>max(N,2) and q not in forbidden and q not in support
         and q%12==(7 if special(i) else 1)
         and all(char(q,p)==t for p,t in zip(support,targets)))
  out.append(q)
  for j,p in enumerate(support):
   assert char(q,p)==targets[j]
   assert (1 if char(q,p)==-1 else 0)==bits(i,j)
   checks['symbol_entries']+=1
   assert char(p,q)==(-1)**((p//2)*(q//2))*targets[j]
   checks['reciprocity_entries']+=1
 assert len(set(out))==k and all(q>max(N,2) and math.gcd(q,12)==1 for q in out)
 assert not(set(out)&(set(seed)|set(forbidden)))
 assert all(e==1 for e in factorint(math.prod(out)).values())
 checks['families']+=1
 return out

for seed in [[],[17],[17,97]]:
 for k in range(5):
  for mask in range(16):
   bits=lambda i,j,mask=mask:(mask>>( (i*(i+2*len(seed)-1)//2+j)%4))&1
   family(seed,k,lambda i:i%2==1,bits,40,{43,61,79})
for theta in [1,73,97]:
 seed=[17]+([] if theta==1 else [theta])
 for d in range(4):
  for mask in range(16):
   bits=lambda i,j,mask=mask:(mask>>((i+j)%4))&1
   q=family(seed,d+1,lambda i:i==d,bits,100,{103,109,127})
   m=math.prod(q);n=17*m
   assert m%12==7 and math.gcd(m,17*theta)==1
   assert n>100 and n*theta>100 and n%12==(n*theta)%12==11
   assert n%17==0
   assert all(e==1 for e in factorint(n*theta).values())
   checks['twist_domains']+=1
result={'status':'PASS','checks':checks,'scope':'Exact finite prime families, every directed and reciprocal symbol, squarefree products, actual n/nθ congruence domains. No point-existence or hosted Lean acceptance.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
