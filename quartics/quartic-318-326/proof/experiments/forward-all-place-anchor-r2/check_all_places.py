#!/usr/bin/env python3
"""Exact algebra plus finite residue sanity only; not Lean/global validation."""
from pathlib import Path
import hashlib,json
import sympy as s
p=Path(__file__).resolve().parent
x,y,z,c,t=s.symbols('x y z c t',nonzero=True)
q=lambda x,y,z:x*x+6*y*y-2*z*z
assert s.expand(q(t*x,t*y,1+t*z)-c-(t*t*q(x,y,z)-(4*z*t+c+2)))==0
assert s.cancel((4*z*t+c+2).subs(t,-(c+2)/(4*z)))==0
X=s.symbols('X')
F=x*x+6*y*y-2*X*X
assert s.diff(F,X).subs(X,1)==-4
assert F.subs(X,1)==q(x,y,1)
assert s.simplify(q(s.sqrt(2),0,1))==0
for prime in s.primerange(5,200):
 assert next(((a,b) for a in range(prime) for b in range(prime) if (a*a+6*b*b-2)%prime==0),None) is not None
 assert s.gcd(prime,4)==1 and s.gcd(prime,6)==1
f=(p/'FiniteAnchorIsotropy318.lean').read_text()
assert 'FiniteField.exists_root_sum_quadratic' in f
h=(p/'PadicAnchorUniversality318.lean').read_text()
assert 'hensels_lemma hnorm' in h and 'z≠0' in h
allp=(p/'ActualAnchorAllPlaces318.lean').read_text()
assert '∀ (p : ℕ) (hp : p.Prime)' in allp
assert 'def LocalGlobalPrinciple : Prop' in allp
assert 'hglobal _ (actual_all_places' in allp
consumer=(p/'PreparedAllPlaceSource318.lean').read_text()
assert '(hglobal : ActualAnchorAllPlaces318.LocalGlobalPrinciple)' in consumer
assert 'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)' in consumer
assert '∀ H : PhysicalAnchorFromHomogeneous318.Homogeneous' not in consumer
assert 'Realization (pre 190)' in consumer and 'Realization (pre 241)' in consumer and 'Realization (pre 292)' in consumer
manifest=json.loads((p/'SOURCE-COPIES.json').read_text())
assert len(manifest['unchanged_sources'])==110 and not manifest['new_sources'] and set(manifest['repaired_sources'])=={'NormalizedPointSigns318'}
for name,row in manifest['unchanged_sources'].items():
 assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==row['source_sha256']
for name in manifest['new_sources']:
 assert 'set_option maxHeartbeats 1000000' in (p/(name+'.lean')).read_text()
print('PASS: exact isotropic-line algebra, Hensel derivative/residual, finite prime sanity, full-place quantifier/explicit global boundary,110 copied sources and one generic-constructor revision. Not a Lean or Hasse-Minkowski proof.')
