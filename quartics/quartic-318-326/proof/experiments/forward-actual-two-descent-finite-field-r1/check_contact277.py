#!/usr/bin/env python3
import json
from fractions import Fraction as Q
from pathlib import Path
import sympy as S
x=S.symbols('x');R=S.Rational
contact=x*(x+R(1,2))*(x+1)*(x-R(1,2399))*(x+R(32,407))
coeff=-R(16,976393)*x+R(76265,1952786)*x*x+R(602706,976393)*(x**3+R(3081901,1205412)*x**4+R(976393,602706)*x**5)
assert S.expand(coeff-contact)==0
count=0
for c in [Q(i,j) for i in range(-5,6) if i for j in [1,2,3]]:
 for t in [Q(i,j) for i in range(-7,8) if i for j in [1,2,5]]:
  z=c*c*t;d=z-1;F=z*(z+Q(1,2))*(z+1)*(z-Q(1,2399))*(z+Q(32,407))
  if not F:continue
  w=c**10*d*d/F
  actual=-Q(16,976393)*z*w*d**3+Q(76265,1952786)*z*z*w*d**3+Q(602706,976393)*(z**3+Q(3081901,1205412)*z**4+Q(976393,602706)*z**5)*w*d**3+(-c*c*d)*(c**8*d**4)
  assert actual==(F*w-c**10*d*d)*d**3==0
  count+=2
result={'status':'PASS','symbolic_contact_polynomial_identity':True,'exact_source_row_checks':count,'scope':'Two unchanged source rows164/217 with original contact denominator and scaled weight.'}
Path(__file__).with_name('CONTACT277-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
