from math import prod
from itertools import combinations
from pathlib import Path
import json
from probe import bs,beta,residues
def cls(p,a):
 v=0
 while a%p==0:a//=p;v+=1
 if p==2:return ((v%2)<<2)^({1:0,3:1,5:2,7:3}[a%8])
 return ((v%2)<<1)^(pow(a%p,(p-1)//2,p)!=1)
def span(v):
 z=[0]
 for u in v:z += [x^u for x in z]
 return set(z)
def reduce(mat,n):
 rows={}
 for x in mat:
  while x:
   i=x.bit_length()-1
   if i not in rows:rows[i]=x;break
   x^=rows[i]
 ker=[]
 for i in range(n):
  if i in rows:continue
  x=1<<i
  for j,r in sorted(rows.items()):
   if (r&x).bit_count()%2:x|=1<<j
  assert not any((r&x).bit_count()%2 for r in mat);ker.append(x)
 return ker
def run(base,qs,ts):
 l=len(base);mat=[]
 def add(p,dim,fn):
  images=[cls(p,a) for a in base]
  imgs=images+[u<<dim for u in images]
  legal=span(fn()); null=reduce(legal,2*dim)
  mat.extend(sum(((u&n).bit_count()%2)<<i for i,u in enumerate(imgs)) for n in null)
 for p in [3]+bs:
  h=cls(p,3*beta);ng=cls(p,-1);assert h&2
  add(p,2,lambda: [h^ng, ng^(h<<2)])
 for p in qs:add(p,2,lambda:[1,2])
 for p in ts:add(p,2,lambda:[1<<2,cls(p,-1)^(2<<2)])
 add(2,3,lambda:[cls(2,5),cls(2,7)^cls(2,3)<<3,cls(2,5)<<3])
 if 13 in base:add(13,2,lambda:[1,1<<2])
 mat.append(1<<(l+base.index(-1)))
 ker=reduce(mat,2*l)
 return [(prod(a for i,a in enumerate(base) if x>>i&1),prod(a for i,a in enumerate(base) if x>>(l+i)&1)) for x in ker]
def main():
 qs=[61,109,6551,17377];ts=[179];core=[-1,2,3]+bs+[13,179];rows=[]
 for k in range(5):
  for sub in combinations(qs,k):
   ker=run(core+list(sub),qs,ts)
   assert len(ker)==1+k
   if not sub:assert ker==[(-3*beta,1)]
   rows.append(dict(chosen_D_primes=list(sub),outer_dimension=len(ker),basis=ker))
 return dict(beta=beta,checked_residues={p:residues(p) for p in [13,179]},all_Selmer_in_core_squared=[(1,1),(-3*beta,1)],outer_only_when_D_primes_individually_adjoined=rows)
if __name__=='__main__':print(json.dumps(main(),indent=2))
