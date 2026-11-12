from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json
finite=0
for t,u in product(range(8),repeat=2):
 if (210*t*t+u*u)%8==0:assert t%2==0 and u%4==0
 finite+=1
for p in [3,5,7]:
 for t,u in product(range(p),repeat=2):
  if (210*t*t+u*u)%p==0:assert u==0
  finite+=1
assert 4-3==1 and -2*12+5*5==1 and 2*60-17*7==1
for t,u in product(range(840),repeat=2):
 if (210*t*t+u*u)%840==0:assert t%2==0 and u%420==0
count=0
for d,r,s in product(range(1,25),range(-16,17),range(-16,17)):
 x,y=Q(r,d),Q(s,d);T=2*x;U=420*y;N=x*x+210*y*y
 assert 210*T*T+U*U==840*N
 if T.denominator==N.denominator==1:assert x.denominator==y.denominator==1
 count+=1
# The tempting half-integer basis is not integral for discriminant -840.
assert (Q(1,2)**2+210*Q(1,2)**2).denominator!=1
out={'status':'PASS','finite_congruence_cases':finite,'full_residue_grid_mod840':840**2,'rational_integrality_and_identity_cases':count,'bezout_checks':3,'negative_half_integer_control':1,'scope':'Exact regression only, not hosted Lean or a class-number/unramifiedness proof.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
