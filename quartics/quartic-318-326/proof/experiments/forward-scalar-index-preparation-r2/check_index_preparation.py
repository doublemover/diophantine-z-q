#!/usr/bin/env python3
"""Exact algebra and finite sanity checks only; not a Lean proof/check."""
from pathlib import Path
import json, hashlib
import sympy as s
p=Path(__file__).resolve().parent
u,v,k,m,D=s.symbols('u v k m D',nonzero=True)
shift=(k*v/u-m)/(k*k+D*u*u)
add=(u*m/k**2-v/k)/(1+D*u*u/k**2)
assert s.cancel(add+u*shift)==0
assert s.cancel(-1/(u*shift)-1/add)==0
q=s.sqrt(2); K=-1+s.Rational(7,4)*q; M=s.Rational(39,8)-s.Rational(9,2)*q
DD=11-6*q; x=1+q
assert s.simplify(1/K-(s.Rational(8,41)+s.Rational(14,41)*q))==0
assert s.simplify((x**4-6*DD*x*x+DD**2)/(x*x+DD)**2-M/K**2)==0
A,B=s.symbols('A B',real=True)
assert s.expand((A+B*q)**2).coeff(q)==2*A*B
assert s.expand((A+B*q)*(A-B*q))==A*A-2*B*B
assert 114444==2**2*28611==3**2*12716==17**2*396
assert 28611%2 and 12716%3 and 396%17
# Exact inequalities as affine functions, not a numerical p-adic assertion.
x,y=s.symbols('x y',integer=True,nonnegative=True)
assert s.expand(2*(3+2*(x+15))-(2*(3+2*x)+29*2))==2
assert s.expand(2*(2+2*(y+1))-2*(2+2*y))==4
# Concrete congruence retains both exact common-index depths for all residues.
def vp(p,n):
 assert n
 n=abs(n);out=0
 while n%p==0:n//=p;out+=1
 return out
for j in range(1000):
 h=64+384*j
 assert vp(2,h)==6 and vp(3,h)==0 and h%64==0
for d in range(1,100):
 n=1+6**21*d
 assert n>1 and n%2==1 and n%3==1
 assert vp(2,n-1)>=21 and vp(3,n-1)>=21
# The written new consumer uses exactly the predecessor's original target.
consumer=(p/'PreparedTwoThreeSource318.lean').read_text()
assert 'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)' in consumer
assert 'Realization (pre 190)' in consumer and 'Realization (pre 241)' in consumer and 'Realization (pre 292)' in consumer
assert 'p.Prime → p≠2 → p≠3 →' in consumer
assert '384∣L → Nat.ModEq 384 h₀ 64 →' in consumer
manifest=json.loads((p/'SOURCE-COPIES.json').read_text())
assert len(manifest['unchanged_sources'])==96 and set(manifest['repaired_sources'])=={'NormalizedPointSigns318'}
for name,row in manifest['unchanged_sources'].items():
 assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==row['source_sha256']
for name in ['ScalarTranslatedIndex318','ScalarIndexValuations318','ScalarHalfTraceDepth318','ScalarTwoThreePreparation318','ScalarPreparedCongruence318','PreparedTwoThreeSource318']:
 assert 'set_option maxHeartbeats 1000000' in (p/(name+'.lean')).read_text()
print('PASS: exact translated chart/sign, actual generator coordinates, norm/half-trace algebra, input constants, depth offsets, congruence sanity, same full-source consumer and96 copied bindings. Not a Lean check.')
