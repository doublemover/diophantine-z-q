"""Literal five-dimensional coefficients vs factored Gauss sums. No Lean."""
import cmath,math,itertools,json
from pathlib import Path
rows=[];maxerr=0.;factorcases=0;boundcases=0
for k in [318,326]:
 for q in range(1,7):
  e=lambda x:cmath.exp(2j*math.pi*(x%q)/q)
  for a in [a for a in range(q) if math.gcd(a,q)==1]:
   for m in [(0,0,0,0,0),(1,-2,3,-4,5),(-1,1,0,2,-3)]:
    direct=sum(e(a*(x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2)+sum(u*v for u,v in zip(m,x))) for x in itertools.product(range(q),repeat=5))
    fact=1+0j
    for c,b in zip([a,a,-a,-a,-k*a],m):fact*=sum(e(c*x*x+b*x) for x in range(q))
    err=abs(direct-fact);maxerr=max(maxerr,err);assert err<2e-8,(k,q,a,m,err)
    assert abs(direct)**2<=32*k*q**5+1e-6
    factorcases+=1
for k in [318,326]:
 for q in list(range(1,50))+[53,106,163,318,326,653]:
  e=lambda x:cmath.exp(2j*math.pi*(x%q)/q)
  aa=[a for a in range(q) if math.gcd(a,q)==1][:6]
  for a in aa:
   for m in [(0,0,0,0,0),(1,-2,3,-4,5),(-1,1,0,2,-3)]:
    fact=1+0j
    for c,b in zip([a,a,-a,-a,-k*a],m):fact*=sum(e(c*x*x+b*x) for x in range(q))
    assert abs(fact)**2<=32*k*q**5+1e-5,(k,q,a,m)
    boundcases+=1
out={'status':'PASS','direct_five_coordinate_factorization_cases':factorcases,'uniform_bound_cases':boundcases,'max_direct_complex_roundoff':maxerr,'constants':{'318':10176,'326':10432},'scope':'Finite direct original q^5 coefficient comparisons and uniform squared-norm regressions, including even/composite/bad-prime/modulus1 cases. No local Lean or global counting claim.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
