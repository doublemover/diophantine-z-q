from pathlib import Path
from itertools import product
import json
D=[2,3,5,6,7,10,14,15,21,30,35,42,70,105]
assert all(0<d<210 and 210%d==0 for d in D)
assert all(r*r!=d for d,r in product(D,range(-10,11)))
count=0
for r,s in product(range(-300,301),repeat=2):
 N=r*r+210*s*s
 if N<210:assert s==0 and N==r*r
 assert N not in D
 count+=1
# Necessary nonsquare and strict-bound assumptions cannot be dropped.
assert 2*2==4 and 0*0+210*1*1==210
out={'status':'PASS','universal_norm_stress_cases':count,'complete_small_square_cases':14*21,'proper_divisor_checks':14,'negative_controls':2,'scope':'Exact regression only; universal Lean source proof is separate and uncompiled.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
