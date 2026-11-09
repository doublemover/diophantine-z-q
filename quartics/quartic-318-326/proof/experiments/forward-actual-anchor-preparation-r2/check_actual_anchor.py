#!/usr/bin/env python3
"""Exact algebra/source binding checks only; no Lean or Hasse-Minkowski test."""
from pathlib import Path
import hashlib,json
import sympy as s
p=Path(__file__).resolve().parent
A,I,S,r,x,y,z,u,v=s.symbols('A I S r x y z u v',nonzero=True)
assert s.cancel(4096*A*S+I-S*(4096*A+I/S))==0
assert s.expand((S*x)**2+6*(S*y)**2-2*(S*z)**2-S*S*(x*x+6*y*y-2*z*z))==0
assert s.expand((S*x)**2-3*(S*r)**2+2*S*S+S*S*(3*r*r-2-x*x))==0
assert s.cancel(3*(u/v)**2-2-(3*u*u-2*v*v)/(v*v))==0
assert s.expand(v*v-(3*u*u-2*v*v)-3*(v*v-u*u))==0
for u in range(8):
 for v in range(8):
  if u%2 and v%2:assert (3*u*u-2*v*v)%8==1
for u in range(3):
 for v in range(3):
  if v:assert (v*v-(3*u*u-2*v*v))%3==0
assert 4096==2**12 and 4*(-3)==-12
N=s.symbols('N',integer=True,nonnegative=True)
assert s.expand((2+2*N)-N)==N+2
# Current-scale identity is consumed from an actual accepted theorem, not unfolded opaquely.
source=(p/'PhysicalAnchorFromHomogeneous318.lean').read_text()
assert 'Current326Bridge.scale_cast' in source
assert 'AnchorAnisotropy.rational_representation_of_homogeneous' in source
assert 'Classical.choice (exists_anchor ns N h)' in source
consumer=(p/'PreparedAnchorSource318.lean').read_text()
assert 'multiplier (2^16) d' in consumer
assert 'CurrentLocalAnchors labels' in consumer
assert '∀ H : PhysicalAnchorFromHomogeneous318.Homogeneous labels (2^16)' in consumer
assert 'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)' in consumer
assert '∀ A : ScalarCompleteSource318.Anchor' not in consumer
assert consumer.index('let labels :=')<consumer.index('∀ᶠ t')<consumer.index('∀ (Pi Mminus')<consumer.index('∃ h : ℕ')
manifest=json.loads((p/'SOURCE-COPIES.json').read_text())
assert len(manifest['unchanged_sources'])==106 and set(manifest['repaired_sources'])=={'NormalizedPointSigns318'}
assert len(manifest['new_sources'])==0
for name,row in manifest['unchanged_sources'].items():
 assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==row['source_sha256']
for name in manifest['new_sources']:
 assert 'set_option maxHeartbeats 1000000' in (p/(name+'.lean')).read_text()
print('PASS: exact physical ratio/scaling, reduced-denominator radicand,2/3 residue/derivative algebra, current-scale and same-h binding,106 source copies. Not a Lean/global arithmetic proof.')
