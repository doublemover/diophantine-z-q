#!/usr/bin/env python3
"""Extend the actual-image regression to every2-adic and real class."""
from pathlib import Path
source=Path(__file__).with_name('check_two_descent_actual_images.py').read_text()
exec(source[:source.index("result={'status'")])
checks['complement_products']=0
for primes,nb,N,B,J in supports:
 n=math.prod(primes);beta=math.prod(B);k=len(primes)
 assert beta%8==1
 K,MM,lam,par=mats(primes,nb)
 classes=[u for u in itertools.product((0,1),repeat=k) if not any(mv(K,list(u)))]
 assert len(classes)==4
 for u in classes:
  M=math.prod(q for q,b in zip(primes,u) if b)
  Mc=math.prod(q for q,b in zip(primes,u) if not b)
  assert M*Mc==n;checks['complement_products']+=1
  assert M%8 in (1,n%8)
  check_point(2,n,M,M%8!=1);checks['two_adic_points']+=1
  x=Q(n+1);A=x+3*n;BB=x-n
  assert M>0 and x>0 and A>0 and BB==1
  checks['real_constructions']+=1
result={'status':'PASS','checks':checks,'scope':'All four actual positive normalized classes at2,3,every support prime and infinity on BOTH produced twists. Literal complementary monomials and actual nonzero local curve/Kummer formulas checked. Does not prove good-prime sufficiency, full Selmer identification or global rational-point existence.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
