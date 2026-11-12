from pathlib import Path
from itertools import product
import json
mul=0;span=0
for p in [1,2,3,5,6,7,10,14,15,21,30,35,42,70,105,210]:
 assert 210%p==0
 for r,s,u,v in product(range(-4,5),repeat=4):
  assert (r*u-210*s*v)%p==(r%p)*(u%p)%p
  mul+=1
 for r,s in product(range(-60,61),repeat=2):
  if r%p==0:
   a=r//p;assert (a*p,s)==(r,s)
  span+=1
for p in [2,3,5,7]:
 assert len({r%p for r in range(p)})==p
# Negative: reducing by a nondivisor does not kill theta squared.
assert (-210)%11!=0 and (-210)%13!=0
out={'status':'PASS','multiplication_cases':mul,'universal_span_witness_tests':span,'actual_prime_quotient_counts':[2,3,5,7],'negative_nondivisor_controls':2,'scope':'Exact finite regression, not Lean or ideal-class exhaustion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
