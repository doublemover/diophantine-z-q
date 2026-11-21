#!/usr/bin/env python3
"""Exact necessary-symbol exhaustion at unscaled slot 190 for square t."""
from math import isqrt, gcd
from pathlib import Path
import json, hashlib
from math import prod
from itertools import product
P0=[5,7,11,13,37,53,109,131,163,439,661,733,1489,1861,2399,1041427]
a=[2,1,2399,407];b=[1,1,-1,32]
pin=Path(__file__).resolve().parent.parent/'linked-detector-finite-saturation-plus5-r1'/'EXACT-CONTACT-TWO-FORM-PLUS5.json'
raw=pin.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='bc5076c3dc48a4a5e8fb3395f517e93e6ba5406fe8044e46058b375e2c75a503'
donor=json.loads(raw); assert donor['omitted_primes']==P0
assert all(all(p%d for d in range(2,isqrt(p)+1)) for p in P0)
def chi(n,p):
 x=pow(n%p,(p-1)//2,p)
 return 0 if x==0 else (1 if x==1 else -1)
delm=[[x*y2-x2*y for x2,y2 in zip(a,b)]for x,y in zip(a,b)]
assert all(gcd(prod(p for p in P0 if p not in (5,7)),delm[i][j])==1 for i,j in product(range(4),repeat=2) if i!=j)
T7=sorted({x*x%7 for x in range(7)})
assert all((ai*T+bi)%7 for ai,bi in zip(a,b) for T in T7)
T5=sorted({x*x%5 for x in range(5)})
assert [T for T in T5 if chi(a[0]*T+b[0],5)==-1]==[1]
signfree=[chi(ai+bi,5) for ai,bi in zip(a,b)]
signsat=[chi(ai,5) for ai in a]
assert signfree==[-1,-1,-1,1] and signsat==[-1,1,1,-1]


def eval(saturation):
 P=[p for p in P0 if p not in saturation and p not in (5,7)]
 base=[aa//prod(p for p in P if aa%p==0) for aa in a]
 def pp(M):return [p for k,p in enumerate(P)if M>>k&1]
 C=[]
 for i in range(4):
  a0,b0=a[i],b[i]
  U=sum(1<<j for j,p in enumerate(P)if a0%p and chi(-a0*b0,p)==1)
  cs={}
  for M in range(1<<len(P)):
    if M&~U:continue
    r=base[i]*prod(pp(M))
    ar=a0//(2 if i==0 else 1)
    rr=r//(2 if i==0 else 1)
    if ar%24==rr%24 and chi(a0,17)==chi(r,17) and chi(r,5)==(chi(a0,5)if 5 in saturation else signfree[i]):
        cs[M]=r
  C.append(cs)
 def pair(i,u,j,v):
  return not (u&v) and all(chi(C[j][v],p)==chi(delm[i][j]*a[i],p) for p in pp(u)) and all(chi(C[i][u],p)==chi(delm[j][i]*a[j],p) for p in pp(v))
 R=[()]; join=[]
 for j in range(4):
  R=[(*t,u)for t,u in product(R,C[j]) if all(pair(i,r,j,u)for i,r in enumerate(t))]
  join.append(len(R))
 return dict(saturated=saturation, individual=[sorted(t.values()) for t in C],
             join_counts=join,all_four=[[C[i][x] for i,x in enumerate(t)]for t in R])

T=[5,11,37,2399]
rows=[]
for mask in range(16):
 S=[p for i,p in enumerate(T)if mask>>i&1]
 r=eval(S)
 assert r['all_four']==([[2,1,2399,407]] if mask==15 else [])
 rows.append(r)
print(json.dumps(dict(actual_h=donor['actual_h'],potential_support=P0,
                      special_saturation_primes=T,free5_signs=signfree,saturated5_signs=signsat,
                      square_T_mod7=T7,final_special_cases=rows),indent=2))
