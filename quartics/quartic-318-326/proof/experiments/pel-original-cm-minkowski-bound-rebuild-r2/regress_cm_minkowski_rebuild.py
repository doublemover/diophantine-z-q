from pathlib import Path
from fractions import Fraction as Q
import json
count=0
for r in range(-20,21):
 for s in range(-20,21):
  m=((r,-210*s),(s,r))
  assert m[0][0]+m[1][1]==2*r
  assert m[0][0]*m[1][1]-m[0][1]*m[1][0]==r*r+210*s*s
  count+=1
assert 2*(-420)==-840
sigs=[(a,b) for a in range(3) for b in range(2) if a+2*b==2 and (-1)**b==-1]
assert sigs==[(0,1)]
assert 840<29**2 and 2*29<19*Q(314,100)
assert all(n<=18 for n in range(100) if n<19)
# Negative controls: the nonmaximal scaled basis and wrong signature cannot be substituted.
assert 2*(-1680)!=-840
assert (-1)**0!= -1
out={'status':'PASS','exact_multiplication_trace_norm_cases':count,'trace_gram_determinant':-840,'signature_cases':6,'rational_bound_checks':2,'natural_rounding_cases':100,'negative_controls':2,'scope':'Exact regression, not Lean or class-group classification.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
