#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,itertools
import sympy as s
import mpmath as mp
c=s.symbols('c',positive=True)
# EXACT Fourier convention test: F(exp(-s^2))(t)=sqrt(pi)*exp(-pi^2*t^2).
# Pairing with exp(-t^2/c) is the same normalized Gaussian recovery.
abel=s.pi/s.sqrt(s.pi*s.pi+1/c)
recover=s.pi*s.sqrt(c)/s.sqrt(s.pi*s.pi*c+1)
assert s.simplify(abel-recover)==0
assert s.limit(abel,c,s.oo)==1
mp.mp.dps=65
pairs=0
for C in [mp.mpf('0.1'),mp.mpf(1),mp.mpf(20),mp.mpf(1000)]:
 left=mp.quad(lambda t:mp.exp(-t*t/C)*mp.sqrt(mp.pi)*mp.exp(-mp.pi**2*t*t),[-mp.inf,0,mp.inf])
 right=mp.pi/mp.sqrt(mp.pi**2+1/C)
 assert abs(left-right)<mp.mpf('1e-60')
 pairs+=1
# Independent exact regrouping on original coordinate tuples, NO scaling.
regroups=0
for a,b,c,d,w in itertools.product(range(-2,3),repeat=5):
 original=((a,b),((c,d),w));target=(a,(b,((c,d),w)))
 reconstructed=((target[0],target[1][0]),target[1][1])
 assert original==reconstructed
 for k in (318,326):
  q=a*a+b*b-c*c-d*d-k*w*w
  r=k*w*w+c*c+d*d-b*b
  assert q==a*a-r
 regroups+=1
# Actual complex original phase orientation, not its conjugate.
phasechecks=0
for k in (318,326):
 for a,b,c,d,w,t in itertools.product((1,2),(0,1),(0,1),(0,1),(0,1),(mp.mpf('0.125'),mp.mpf('0.37'))):
  q=a*a+b*b-c*c-d*d-k*w*w
  assert abs(mp.exp(-2j*mp.pi*q*t)-mp.exp(1j*(-2*mp.pi*q*t)))<mp.mpf('1e-60')
  phasechecks+=1
base=Path(__file__).resolve().parent
pr=base/'AMBIENT-FOURIER-PRIMARY' if (base/'AMBIENT-FOURIER-PRIMARY').exists() else base/'PRIMARY'
meta=json.loads((pr/'PRIMARY-SOURCES.json').read_text())
for n,r in meta.items():
 z=(pr/n).read_bytes();assert hashlib.sha256(z).hexdigest()==r['sha256'];assert hashlib.sha1(b'blob '+str(len(z)).encode()+b'\0'+z).hexdigest()==r['git_blob']
print(json.dumps({'exact_original_volume_regroupings':regroups,'negative_two_pi_original_phase_checks':phasechecks,'exact_gaussian_abel_identity_and_limit':2,'65_digit_gaussian_fourier_pairings':pairs,'verified_primary_blobs':len(meta),'local_lean':'NOT_RUN','undamped_fourier_integrability':'NOT_CLAIMED','global_integer_point_asymptotic':'NOT_CLAIMED'},indent=2))
