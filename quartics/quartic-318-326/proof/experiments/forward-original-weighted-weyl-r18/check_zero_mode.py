"""Exact phase/scaling and finite actual zero-mode coefficient checks. No Lean."""
from fractions import Fraction as F
import cmath,itertools,math,json
from pathlib import Path
exact=0
for B in [F(1,2),F(3),F(7,3),F(-2)]:
 for q in range(1,8):
  for beta in [F(-2,3),F(0),F(5,7)]:
   for Q in [-318,-3,0,7,326]:
    assert -2*Q*(-beta)==2*beta*Q
    assert (B/q)**5/B**2==B**3/F(q)**5
    exact+=1
rows=[];coeff={}
for k in [318,326]:
 for q in range(1,7):
  counts=[0]*q
  for x in itertools.product(range(q),repeat=5):
   counts[(x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2)%q]+=1
  value=sum(sum(c*cmath.exp(2j*math.pi*a*t/q) for t,c in enumerate(counts)) for a in range(q) if math.gcd(a,q)==1)/q**5
  coeff[k,q]=value
  if q==1:expected=F(1)
  elif q in [2,3,5]:expected=F(counts[0],q**4)-1
  elif q==4:
   n2=sum(1 for x in itertools.product(range(2),repeat=5) if (x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2)%2==0)
   expected=F(counts[0],4**4)-F(n2,2**4)
  else:expected=coeff[k,2]*coeff[k,3]
  assert abs(value-complex(expected))<2e-12,(k,q,value,expected)
  rows.append(dict(kappa=k,q=q,unit_zero_mode=[value.real,value.imag],independent_count_or_crt_value=str(expected)))
out={'status':'PASS','exact_phase_and_B_cubic_normalizations':exact,'actual_zero_mode_coefficient_cases':rows,'scope':'Finite actual unit-frequency zero modes checked against independent original counts/CRT; exact negative-to-positive phase reflection and B^5/B^2=B^3. Infinite cutoff limits and normalized original weight remain source obligations. No Lean execution.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
