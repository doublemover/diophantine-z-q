#!/usr/bin/env python3
"""Direct actual squareclass signatures plus explicit local-point constructions."""
from pathlib import Path
import itertools,json,math
src=Path(__file__).with_name('check_two_descent_local_points.py').read_text()
exec(src[:src.index('for primes,nb,N,B,J in supports:')])
checks.update(actual_local_classes=0,literal_signature_candidates=0,unit_square_comparisons=0)
def sig(q,x):
 e=vp(q,x);u=Q(x)/Q(q)**e
 z=u.numerator*pow(u.denominator,-1,q)%q
 return (e%2,0 if pow(z,(q-1)//2,q)==1 else 1)
for q in (5,7,11,13,17,19):
 for A,D in itertools.product(range(-13,14),repeat=2):
  if not A or not D or A%q==0 or D%q==0:continue
  for e,f in itertools.product((0,1),repeat=2):
   quotient=Q(q)**(e-f)*Q(A,D)
   ee=vp(q,quotient);uu=quotient/Q(q)**ee
   z=uu.numerator*pow(uu.denominator,-1,q)%q
   if ee%2==0 and pow(z,(q-1)//2,q)==1:
    assert e==f and sig(q,A)==sig(q,D)
    checks['unit_square_comparisons']+=1
for primes,nb,N,B,J in supports:
 n=math.prod(primes);k=len(primes);ones=(1,)*k
 monos={u:math.prod(p for p,b in zip(primes,u) if b) for u in itertools.product((0,1),repeat=k)}
 torsion=[{(sig(q,n**a*3**b),sig(q,(-n)**b)) for a,b in itertools.product((0,1),repeat=2)} for q in primes]
 firsts={(delta,u):[sig(q,3**delta*M) for q in primes] for u,M in monos.items() for delta in (0,1)}
 seconds={v:[sig(q,L) for q in primes] for v,L in monos.items() if L%3==1}
 found=[]
 for (delta,u),ss in firsts.items():
  for v,tt in seconds.items():
   checks['literal_signature_candidates']+=1
   if all((s,t) in T for s,t,T in zip(ss,tt,torsion)):
    assert delta==0 and not any(v)
    found.append(u)
 assert len(found)==4
 K,MM,lam,par=mats(primes,nb)
 expected={u for u in monos if not any(mv(K,list(u)))}
 assert set(found)==expected
 checks['actual_local_classes']+=len(found)
 for u in found:
  M=monos[u]
  for q in primes:
   check_point(q,n,M,M%q==0);checks['support_prime_points']+=1
  check_point(3,n,M,M%3==2);checks['three_adic_points']+=1
result={'status':'PASS','checks':checks,'scope':'Literal support-prime squareclass invariants compared with actual four torsion pairs, exact Q3 condition, four resulting classes on each actual support, and explicit original cubic/Kummer local witnesses for every class. No full Selmer or global rational-point conclusion.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
