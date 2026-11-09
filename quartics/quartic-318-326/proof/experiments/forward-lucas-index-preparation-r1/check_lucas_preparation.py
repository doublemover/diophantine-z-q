#!/usr/bin/env python3
"""Exact polynomial/copy checks and finite sanity checks, not Lean validation."""
from pathlib import Path
import hashlib,json
import sympy as s
p=Path(__file__).resolve().parent
u,v,a,z=s.symbols('u v a z')
F=lambda x,y:y*y-a*y*x+x*x
assert s.expand(F(v,a*v-u)-F(u,v))==0
assert s.cancel((v*v-a*(a-2)*v*z+(a-2)**2*z*z).subs(z,u/(a-2))-F(u,v))==0
x=s.symbols('x',integer=True)
assert s.expand(3723*(2*x+1)**2-3723-14892*(x+x*x))==0
def vp(p,n):
 assert n
 out=0
 while n%p==0:n//=p;out+=1
 return out
for A in range(6,11):
 for B in range(6):
  R=2**A*3**B;mod=6*R
  for j in range(20):
   h=R+mod*j
   assert vp(2,h)==A and vp(3,h)==B and h%64==0
  for d in range(1,12):
   label=1+6**(A+B+15)*d
   assert label>=3 and label%2==1 and label%3==1
   assert vp(2,label-1)>=A+15 and vp(3,label-1)>B
# The huge constructed labels use the proved Lucas theorem, not this finite sample.
for a in (7,13,19,25):
 k=2*(a-2);u,v=0,1
 for _ in range(k):u,v=v,a*v-u
 assert u%(a-2)==0
 z=u//(a-2)
 assert v>0 and z>0 and v%2==1 and z%2==1
 assert v*v-a*(a-2)*v*z+(a-2)**2*z*z==1
manifest=json.loads((p/'SOURCE-COPIES.json').read_text())
assert len(manifest['unchanged_sources'])==97 and not manifest['repaired_sources']
for name,row in manifest['unchanged_sources'].items():
 assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==row['source_sha256']
assert manifest['new_sources']==['ScalarPreparedResidues318','FixedArithmeticLabels318','PreparedLucasSource318']
src=(p/'PreparedLucasSource318.lean').read_text()
assert 'let labels := FixedArithmeticLabels318.labels a A₂ A₃ d hd' in src
assert src.index('let labels :=')<src.index('∀ᶠ t')<src.index('∀ (Pi Mminus')<src.index('∃ h : ℕ')
assert 'p.Prime → p≠2 → p≠3 →' in src
assert 'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)' in src
assert 'ScalarPreparedCongruence318.continuity_preserves_units' not in src
for name in manifest['new_sources']:
 assert 'set_option maxHeartbeats 1000000' in (p/(name+'.lean')).read_text()
print('PASS: exact Lucas invariant/source relabeling, literal beta, adjustable depth/residue sanity, same object/choice-order consumer,97 copied sources. Not a Lean check.')
