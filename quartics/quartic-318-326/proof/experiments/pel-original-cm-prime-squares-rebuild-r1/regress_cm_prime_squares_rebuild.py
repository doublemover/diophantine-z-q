from pathlib import Path
from itertools import product
import json
count=0
for p,A,C in [(2,53,1),(3,47,2),(5,17,2),(7,13,3)]:
 assert A*p*p-C*210==p
 q=210//p
 for a,b,c,d in product(range(-5,6),repeat=4):
  left=(p*p*a*c-210*b*d,p*a*d+p*b*c)
  witness=(p*a*c-q*b*d,a*d+b*c)
  assert left==(p*witness[0],p*witness[1]);count+=1
# wrong sign and missing Bezout coefficient fail
assert 53*4+210!=2 and 47*9-210!=3
out={'status':'PASS','universal_product_identity_tests':count,'exact_bezout_identities':4,'negative_controls':2,'scope':'Exact regression only; no Lean or class-number assertion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
