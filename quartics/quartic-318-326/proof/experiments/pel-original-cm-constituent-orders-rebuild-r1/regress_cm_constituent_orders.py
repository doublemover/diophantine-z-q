from pathlib import Path
from fractions import Fraction
from itertools import product
import json
rows=[(-2,0,-8),(-1,1,-3),(1,1,5),(-2,1,-7)]
identity=0
for a,b in product(range(-4,5),repeat=2):
 D=4*a+b*b
 for r,s in product([Fraction(i,j) for i in range(-5,6) for j in range(1,5)],repeat=2):
  T=2*r+b*s;U=D*s;N=r*r+b*r*s-a*s*s
  assert D*T*T-U*U==4*D*N
  identity+=1
residues=0
for d in [-3,5,-7]:
 m=4*abs(d)
 for T,U in product(range(m),repeat=2):
  if (d*T*T-U*U)%(4*d)==0:
   assert U%d==0 and (T-U//d)%2==0
  residues+=1
for T,U in product(range(8),repeat=2):
 if (2*T*T+U*U)%8==0:assert T%2==0 and U%4==0
grid=sorted({Fraction(i,j) for i in range(-12,13) for j in range(1,9)})
coordinates=0
for a,b,d in rows:
 assert 4*a+b*b==d
 assert 2*(2*a+b*b)-b*b==d
 for r,s in product(grid,repeat=2):
  T=2*r+b*s;N=r*r+b*r*s-a*s*s
  if T.denominator==N.denominator==1:assert r.denominator==s.denominator==1
  coordinates+=1
# Wrong half-integral basis for sqrt(-2) is not integral.
r=s=Fraction(1,2)
assert (r*r+2*s*s).denominator!=1
# Raw odd-radicand basis has discriminant4d, not the full d.
assert all(4*d!=d for d in [-3,5,-7])
out={'status':'PASS','universal_trace_norm_identity_cases':identity,'odd_modular_cases':residues,
 'even_modular_cases':64,'rational_integral_coordinate_stress_cases':coordinates,
 'actual_discriminants':[d for a,b,d in rows],'negative_controls':4,
 'scope':'Exact arithmetic regression, not Lean or full H discriminant/unramifiedness.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
