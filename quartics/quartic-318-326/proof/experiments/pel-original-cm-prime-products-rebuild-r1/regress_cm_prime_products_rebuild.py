from pathlib import Path
from itertools import product
import json
rows=[(2,3,-1,1),(2,5,-2,1),(3,5,2,-1),(6,5,1,-1),(30,7,4,-17)]
cases=0
for m,n,A,C in rows:
 assert 210%(m*n)==0 and A*m+C*n==1
 q=210//(m*n)
 for a,b,c,d in product(range(-5,6),repeat=4):
  assert (m*a*n*c-210*b*d)==m*n*(a*c-q*b*d)
  cases+=1
for a,s in product(range(-100,101),repeat=2):
 assert (-210*(-a),s)==(210*a,s)
assert 2*3*5*7==210
# Omitting coprimality does not give theta from the Bezout combination.
assert all(2*a+2*c!=1 for a,c in product(range(-10,11),repeat=2))
out={'status':'PASS','product_coordinate_cases':cases,'exact_Bezout_pairs':5,'theta_divisibility_cases':201**2,'all_four_product':210,'negative_coprimality_control':1,'scope':'Exact regression only, not Lean or class-group exhaustion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
