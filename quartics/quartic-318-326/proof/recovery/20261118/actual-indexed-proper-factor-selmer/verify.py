import json
from itertools import combinations
from math import prod,isqrt
import original_probe
from support import run,bs
def main():
 qs=[61,109,6551,17377]; ts=[179,1453337,3666241]; ps=ts[1:]
 ms=[55766749841841019897760,11291822867144728666368000]
 residues={}
 for p,m in zip(ps,ms):
  assert all(p%k for k in range(2,isqrt(p)+1)) and p%8==1
  o=original_probe.probe(p,j=2,forceM=m); assert (o['D']-4)%p==0 and (o['D']-4)%(p*p)
  residues[p]=o
 base=[-1,2,3]+bs+[13]+ts
 tab=[]
 for k in range(5):
  for subset in combinations(qs,k):
   ker=run(base+list(subset),qs,ts)
   d=1 if k<3 and tuple(subset)!=(61,17377) else 3 if k==4 else 2
   assert len(ker)==d
   tab.append(dict(individual_D_factors=subset,outer_dimension_before_whole_D_T=d,basis=ker))
 assert prod(ps)%8==1 and prod(qs)%8==7
 return dict(true_p_squared=residues,local_intersections=tab)
if __name__=='__main__':print(json.dumps(main(),indent=2))
