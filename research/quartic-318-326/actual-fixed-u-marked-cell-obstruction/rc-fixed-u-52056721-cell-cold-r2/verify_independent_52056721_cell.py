import json
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
from math import isqrt, prod
from sympy import sqrt_mod
from hashlib import sha256
from sys import argv
P,A=map(Path,argv[1:])
assert sha256(P.read_bytes()).hexdigest()=='1bafc111ab865a630ede511759c68f9aeee51e254d58cd4dab424bed84a35eb8'
assert sha256(A.read_bytes()).hexdigest()=='f5dbe608ef26c9bde7a3ff31f40770ba9924fd4e9071e49520761ac3f39e7b64'
d=json.loads(P.read_bytes()); old=json.loads(A.read_bytes())
p=52056721;p2=p*p
assert all(p%d for d in range(2,isqrt(p)+1))
ni,W,*_=next(x for x in old['old_cells_W_a_unit_b_unit'] if x[0]==p)
m=[[(v>>j)&1 for j in range(38)]+[t] for v,t in d['affine_rows']]
cur=0; piv=[]
for j in range(38):
 k=next((i for i in range(cur,len(m)) if m[i][j]),None)
 if k is None: continue
 m[k],m[cur]=m[cur],m[k]
 for l in range(len(m)):
  if l!=cur and m[l][j]: m[l]=[x^y for x,y in zip(m[l],m[cur])]
 piv.append(j);cur+=1
free=[i for i in range(38) if i not in piv];assert len(free)==4
assert not any(any(row) for row in m[cur:])
S=d['finite_support'];g=[]
for f in product([0,1],repeat=4):
 v=[0]*38
 for i,z in zip(free,f):v[i]=z
 for i,j in enumerate(piv):v[j]=m[i][-1]^(sum(a*b for a,b in zip(m[i][:-1],v))%2)
 assert all(sum(v[j]*((row>>j)&1) for j in range(38))%2==t for row,t in d['affine_rows'])
 g.append(tuple(prod(a for a,s in zip(S,v[19*i:19*(i+1)]) if s) for i in (0,1)))
def lg(q):
 q=q%p
 assert q
 return pow(q,(p-1)//2,p)==p-1
mask=sum(int(lg(q))<<(19+j) for j,q in enumerate(S))
ids=[3,7,9,13,16,22,23]
z=t=0
for i in ids:
 a,b=d['affine_rows'][i]
 z^=a; t^=b
assert z==mask==61262004224 and t==0
allowed=sorted(set(tuple(lg(x) for x in pair) for pair in g))
b=d['b']; t=Q(*d['t']); l=Q(*d['lambda_'])
red=lambda x: x.numerator*pow(x.denominator,-1,p2)%p2
q1=red(b*(W*W-t));q2=red(W*W+l)
assert q1%p and q2%p and W%p
zs=[int(sqrt_mod(xx,p2)) for xx in (q1,q2)]
rows=[]
for s,t in product([1,-1],repeat=2):
 Z=[W,s*zs[0]%p2,t*zs[1]%p2,1]
 vals=[sum(c*a for c,a in zip(row,Z))%p2 for row in d['normalized_tangent_coefficients']]
 assert all(vals)
 ords=[int(v%p==0) for v in vals]
 chars=tuple(lg((vals[i]//p**ords[i])*(vals[j]//p**ords[j])) for i,j in ((1,2),(0,2)))
 v=(ords[1]+ords[2],ords[0]+ords[2])
 assert v==(0,0) and chars==(True,True) and allowed==[(False,False)]
 rows.append(dict(phase=[s,t], roots=Z, Ltangent_mod_p2=vals,tangent_orders=ords,product_orders=list(v),product_nonsquare_bits=chars))
print(json.dumps(dict(p=p,W=W,root_residues_base=zs,global_affine_candidates=len(g),global_unit_profiles=allowed,certifying_input_rows_zero_based=ids,local_sign_branches=rows),indent=2))
