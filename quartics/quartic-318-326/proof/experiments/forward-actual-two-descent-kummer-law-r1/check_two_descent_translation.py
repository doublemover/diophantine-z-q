#!/usr/bin/env python3
"""Exact torsion identities, involution and actual signed local witnesses."""
from pathlib import Path
source=Path(__file__).with_name('check_two_descent_all_bad.py').read_text()
exec(source[:source.rindex("\nresult=")])
import sympy as sp
n,x,y=sp.symbols('n x y');A=x+3*n;B=x-n
X=-3*n*B/A;Y=-12*n*n*y/A**2
assert sp.factor(X+3*n-12*n*n/A)==0
assert sp.factor(X-n+4*n*x/A)==0
assert sp.factor(Y**2-X*(X-n)*(X+3*n)-144*n**4/A**4*(y*y-x*B*A))==0
assert sp.factor(-3*n*(X-n)/(X+3*n)-x)==0
assert sp.factor(-12*n*n*Y/(X+3*n)**2-y)==0
assert sp.factor((X+3*n)-3*A*(2*n/A)**2)==0
assert sp.factor((X-n)-(-n)*B*(2*y/(B*A))**2-4*n/(B*A*A)*(y*y-x*B*A))==0
checks.update(symbolic_translation_identities=7,exact_involutions=0,signed_local_points=0,signed_kummer_residuals=0,representative_toggle_identities=0)
for nn in range(1,21):
 for xx in (Q(k,7) for k in range(-30,31)):
  if not xx or not xx-nn or not xx+3*nn:continue
  yy=Q(2,3);XX=-3*nn*(xx-nn)/(xx+3*nn);YY=-12*nn*nn*yy/(xx+3*nn)**2
  assert XX and XX-nn and XX+3*nn
  assert -3*nn*(XX-nn)/(XX+3*nn)==xx
  assert -12*nn*nn*YY/(XX+3*nn)**2==yy
  checks['exact_involutions']+=1

def signed_point(q,nn,M,first):
 k=max(0,vp(q,Q(nn)))+3;KK=64+12*k;b=Q(q)**k
 if first:
  xx=Q(nn)+b*b;AA=xx+3*nn;BB=xx-nn
  r=root(q,xx/nn,KK);s=root(q,AA/(4*nn),KK);yy=2*nn*b*r*s;u0=2*s;v=b;c=Q(nn)
 else:
  xx=1/(b*b);AA=xx+3*nn;BB=xx-nn
  r=root(q,AA/xx,KK);s=root(q,BB/xx,KK);yy=r*s/(b**3);u0=r/b;v=s/b;c=Q(1)
 t=root(q,Q(M)/c,KK);u=u0/t
 XX=-3*nn*BB/AA;YY=-12*nn*nn*yy/AA**2
 uu=u*2*nn/AA;vv=v*2*yy/(BB*AA)
 assert XX and XX-nn and XX+3*nn and uu and vv
 assert vp(q,YY*YY-XX*(XX-nn)*(XX+3*nn))>=20
 assert vp(q,XX+3*nn-3*M*uu*uu)>=20
 assert vp(q,XX-nn+nn*vv*vv)>=20
 checks['signed_local_points']+=1;checks['signed_kummer_residuals']+=2
for primes,nb,N,B0,J in supports:
 nn=math.prod(primes);k=len(primes);K,MM,lam,par=mats(primes,nb)
 for u in itertools.product((0,1),repeat=k):
  M=math.prod(q for q,b in zip(primes,u) if b)
  Mc=math.prod(q for q,b in zip(primes,u) if not b)
  for delta,eps in itertools.product((0,1),repeat=2):
   assert 3*(3**delta*M)==3**(delta^1)*M*(3**delta)**2
   assert (-nn)*((-1)**eps*M)==(-1)**(eps^1)*Mc*M*M
   checks['representative_toggle_identities']+=2
  if not any(mv(K,list(u))):
   signed_point(2,nn,M,M%8!=1)
   signed_point(3,nn,M,M%3==2)
   for q in primes:signed_point(q,nn,M,M%q==0)
result={'status':'PASS','checks':checks,'scope':'Actual rational torsion translation/involution, literal signed representative rescaling, and all eight signed actual local classes at2,3,support,infinity on both produced twists. No good-prime or global Selmer/rational-point existence claim.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
