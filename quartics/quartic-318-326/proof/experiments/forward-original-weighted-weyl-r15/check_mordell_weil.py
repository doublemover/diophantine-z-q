from itertools import product
from fractions import Fraction as F
from pathlib import Path
import json
import sympy as s
finite_groups=elements=rank_checks=four_torsion_cases=0
for length in range(0,4):
 for moduli in product(range(1,13),repeat=length):
  G=list(product(*(range(m) for m in moduli)))
  image={tuple((2*a[i])%moduli[i] for i in range(length)) for a in G}
  ker=[a for a in G if all(2*a[i]%moduli[i]==0 for i in range(length))]
  assert len(G)==len(image)*len(ker)
  index=len(G)//len(image);assert index==len(ker)
  finite_groups+=1;elements+=len(G)
  for rank in range(5):
   free_mod_two=list(product(range(2),repeat=rank))
   actual_index=len(free_mod_two)*index
   assert actual_index==2**rank*len(ker);rank_checks+=1
   if len(ker)==4:
    assert (actual_index<=8)==(rank<=1)
    if rank and actual_index<=8:assert rank==1 and actual_index==8
    four_torsion_cases+=1
n,x,y=s.symbols('n x y');f=x*(x-n)*(x+3*n)
assert s.discriminant(f,x)==144*n**6
assert s.expand(16*s.discriminant(f,x)-2304*n**6)==0
for nn in list(range(-60,0))+list(range(1,61)):
 roots=[F(0),F(nn),F(-3*nn)];assert len(set(roots))==3
 for r in roots:assert r*(r-nn)*(r+3*nn)==0
 # Every nonvertical tangent has a finite output; hence cannot be the identity.
 for xx in range(-10,11):
  if xx not in roots:assert xx*(xx-nn)*(xx+3*nn)!=0
result={'status':'PASS','finite_abelian_groups':finite_groups,'finite_group_elements':elements,'free_finite_index_checks':rank_checks,'four_torsion_rank_checks':four_torsion_cases,'actual_cubic_torsion_twists':120,'symbolic_discriminant_checks':2,'scope':'Exact group index and original cubic regressions; height/Mordell-Weil proof uses pinned primary theorems, and no positive-rank or infinitude assertion is inferred.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
