from fractions import Fraction as F
from pathlib import Path
import json
counts={'actual_common_points':0,'inverse_u':0,'coefficient_matching':0,'negative_sign_control':0}
for n in map(F,range(-4,5)):
 for u in [F(k,2) for k in range(-20,21)]:
  for v in [F(k,8) for k in range(-48,49)]:
   if v==0 or v-u**3-2*n*u*u*v+3*n*n*u*v*v!=0:continue
   f=1-2*n*u*u+3*n*n*u*v
   assert f!=0
   e=1/f;inverse_u=e*u*u/v
   assert u*inverse_u==1
   counts['actual_common_points']+=1;counts['inverse_u']+=1
   for b in [F(0),F(2,3),F(-7,5)]:
    assert b*inverse_u==b/u;counts['coefficient_matching']+=1
   if u*u!=1:
    assert inverse_u!=u;counts['negative_sign_control']+=1
assert all(counts.values())
out={'status':'PASS','scope':'Exact finite original-chart transition algebra only; not sheaf descent,invertibility,Lean or divisor validation','counts':counts}
Path(__file__).with_name('IDEAL-SHEAF-TRANSITION-REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
