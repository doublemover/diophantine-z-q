#!/usr/bin/env python3
from pathlib import Path
import json,math
H=Path(__file__).resolve().parent
O=H.parent/'forward-canonical-cm-count-r1'
i=json.loads((O/'intake.json').read_text())
for n in i['order']:assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n
cases=0;parity=0
for p in range(2,2000):
 if any(p%q==0 for q in range(2,math.isqrt(p)+1)):continue
 r=math.isqrt(p)
 reps=[(a,b) for a in range(-r,r+1) for b in range(-r,r+1) if a*a+b*b==p]
 for a,b in reps:
  for c,d in reps:
   assert ((a*c+b*d)*(a*c-b*d))%p==0
   assert a*a in (c*c,d*d)
   for ds in (d,-d):
    dot=a*c+b*ds
    if dot%p==0:
     k=dot//p
     assert k in (-1,0,1)
     assert (a*a==ds*ds) if k==0 else (a*a==c*c)
   cases+=1
   if b%2==0 and c%2==1:
    assert a*a==c*c
    parity+=1
assert 3*3+4*4==0*0+5*5==25 and 3*3 not in (0*0,5*5)
assert 2*2+1*1==1*1+2*2==5 and 2*2!=1*1
print(json.dumps({'unchanged_r1_sources':len(i['order']),'prime_norm_pairs':cases,
 'odd_real_even_imaginary_pairs':parity,'negative_controls':['composite_norm25','missing_parity5'],
 'universal_CM_proved':False,'Lean_run':False},indent=2))
