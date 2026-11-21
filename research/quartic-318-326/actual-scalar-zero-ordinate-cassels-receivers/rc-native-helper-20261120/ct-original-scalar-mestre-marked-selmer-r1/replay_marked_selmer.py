#!/usr/bin/env python3
import json
from math import prod
from pathlib import Path
P=Path(__file__).resolve().parent
S=json.loads((P.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json').read_text())
aux=json.loads((P.parent.parent/'joined-work-20261120/rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json').read_text())
B=[5,11,17,163,661,733,1489,1861]
V=[131,6551,2470991,16782959]
uq=[82,684]+[a['theta_factor'] for a in aux]
assert [a['prime'] for a in aux]==V[2:] and uq==[82,684,2223081,13715188]
assert prod(B)==114444*S['R_input']//(17*12**2)
K=B+V
def finite_bit(p,q):
 assert q%p
 n=pow(q%p,(p-1)//2,p); assert n in [1,p-1]
 return int(n==p-1)
diag={p:finite_bit(p,u) for p,u in zip(V,uq)}
diag|={p:sum(finite_bit(p,q) for q in B if q!=p)%2 for p in B}
ell={p:diag[p]^(sum(finite_bit(p,q) for q in K if q!=p)%2) for p in K}
U='P'
def bit(p,q):
 if p==U:
  if q==-1:return 0
  return ell[q]
 if q==U:return ell[p]
 return finite_bit(p,q)
def make(L):
 n=len(L); rows=[]
 for i,p in enumerate(L):
  l=sum(bit(p,q)<<j for j,q in enumerate(L) if i!=j)
  D=diag.get(p,l.bit_count()%2)
  Ap=l^(D<<i); k=bit(p,-1)
  if p==5:rows.extend([Ap,(Ap<<n)^(D<<i)])
  else:rows.extend([Ap^(k<<(n+i)),(Ap<<n)^(k<<(n+i))^(bit(p,5)<<i)])
 return rows+[sum(bit(p,-1)*(2**i+2**(n+i)) for i,p in enumerate(L))]
def solve(rows,N):
 work={}
 for u in rows:
  while u:
   j=u.bit_length()-1
   if j in work:u^=work[j]
   else:work[j]=u;break
 v=[]
 for i in [j for j in range(N) if j not in work]:
  x=1<<i
  for k in sorted(work):
   if (x&work[k]).bit_count()%2:x^=1<<k
  v.append(x)
 assert all((x&r).bit_count()%2==0 for x in v for r in rows)
 return len(work),sorted(v)
def oldrow(p):return sum(bit(p,q)<<i for i,q in enumerate(B))
ol=make(B)
rk0,bs0=solve(ol,16);assert rk0==14 and bs0==[57599,57600]
rk1,bs1=solve(ol+[oldrow(131),oldrow(131)<<8],16);assert rk1==15 and bs1==[511]
r=make(K); rk,bs=solve(r,24); assert rk==23 and bs==[4351]
rr=make(K+[U]); rkk,bss=solve(rr,26)
assert rkk==24 and bss==[7936,8447] and ell[5]==0
assert [ell[p] for p in K]==[0,0,1,0,1,1,0,1,0,0,1,0]
assert prod(V)%4==1 and prod(V)%24==13
assert all(finite_bit(p,5)==0 for p in V)
assert 19*15*20==4*1425 and 1425%8==1
print(json.dumps(dict(h=S['h'],beta=prod(B),visible=K,true_d_stripped_bits=[diag[p] for p in K],
 old_only=dict(rank=rk0,base_masks=bs0,base_after_p131=bs1),
 visible_only=dict(rows=r,rank=rk,positive_kernel_masks=bs),
 conditional_one_unseen=dict(aggregate_bits=[ell[p] for p in K],prime_one_mod_four=True,
 rows=rr,rank=rkk,positive_kernel_masks=bss,total_Selmer_dimension=3)),indent=2,sort_keys=True))
