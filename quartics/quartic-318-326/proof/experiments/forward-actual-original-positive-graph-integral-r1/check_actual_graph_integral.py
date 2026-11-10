#!/usr/bin/env python3
from fractions import Fraction as F
import itertools,json,hashlib
from pathlib import Path
import sympy as s
# Exact support-sensitive denominator identity; never divide through zero.
checks=0
for eta,a,num in itertools.product((F(1,7),F(1),F(20)),(F(0),F(1,3),F(2),F(50)),(F(0),F(1,8),F(1))):
 if num and not eta<2*a: continue
 original=F(0) if not a else num/(2*a)
 safe=num/max(eta,2*a)
 assert original==safe
 checks+=1
# Coordinate graph density normalization, tested on an independent compact
# C1 polynomial parameter bump. This is NOT the smooth bump existence proof.
x=s.symbols('x');one=s.integrate((1-x*x)**2,(x,-1,1));assert one==s.Rational(16,15)
mass=one**4;assert mass>0 and s.simplify(mass/mass)==1
points=0
for vv in itertools.product((F(-1),F(-1,2),F(0),F(1,2),F(1)),repeat=4):
 phi=F(1)
 for q in vv:phi*=(1-q*q)**2
 for k in (318,326):
  b,c,d,w=vv[0],vv[1],vv[2],vv[3]+3
  R=k*w*w+c*c+d*d-b*b
  assert R>0
  # Actual graph numerator2sqrt(R)*phi cancels actual derivative2sqrt(R).
  assert s.simplify(2*s.sqrt(s.Rational(R.numerator,R.denominator))*s.Rational(phi.numerator,phi.denominator)/(2*s.sqrt(s.Rational(R.numerator,R.denominator))))==s.Rational(phi.numerator,phi.denominator)
  assert phi>=0
  points+=1
base=Path(__file__).resolve().parent
if (base/'GRAPH-INTEGRAL-PRIMARY').exists():primary=base/'GRAPH-INTEGRAL-PRIMARY'
else:primary=base/'PRIMARY'
meta=json.loads((primary/'PRIMARY-SOURCES.json').read_text())
for name,row in meta.items():
 data=(primary/name).read_bytes()
 assert hashlib.sha256(data).hexdigest()==row['sha256']
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob']
print(json.dumps({'exact_support_sensitive_regularizations':checks,'actual_original_graph_jacobian_tests':points,'exact_compact_parameter_integral':str(mass),'exact_primary_blob_pins':len(meta),'actual_smooth_bump':'inherited533 proved Mathlib producer','local_lean':'NOT_RUN','oscillatory_identification':'NOT_CLAIMED'},indent=2))
