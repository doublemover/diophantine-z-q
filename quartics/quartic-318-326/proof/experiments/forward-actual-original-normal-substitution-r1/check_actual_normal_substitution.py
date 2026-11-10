#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
import sympy as sy
import mpmath as mp
import json,hashlib,itertools
k,a,b,c,d,w=sy.symbols('k a b c d w');R=k*w*w+c*c+d*d-b*b;Q=a*a+b*b-c*c-d*d-k*w*w
assert sy.expand(Q-(a*a-R))==0
assert sy.diff(Q,a)==2*a
bounds=0
for A,B,aa,rr in itertools.product((F(1,4),F(1)),(F(3),F(10)),(F(3,2),F(2),F(5)),(F(-10),F(0),F(13),F(100000))):
 if not A<aa<B:continue
 s=aa*aa-rr
 assert A*A-rr<s<B*B-rr
 assert (s+rr)==aa*aa
 assert (2*aa)*(F(7,3)/(2*aa))==F(7,3)
 bounds+=1
mp.mp.dps=60
comparisons=0
for kk in (318,326):
 for v in ((0,0,0,0),(1,2,0,1),(-2,1,3,2)):
  bb,cc,dd,ww=v;rad=mp.mpf(kk*ww*ww+cc*cc+dd*dd-bb*bb)
  for alpha in (mp.mpf(0),mp.mpf('0.125'),mp.mpf('0.7')):
   weight=lambda x:(1-(x-2)**2)**2
   left=mp.quad(lambda x:weight(x)*mp.exp(1j*alpha*(x*x-rad)),[1,2,3])
   right=mp.quad(lambda s:weight(mp.sqrt(s+rad))/(2*mp.sqrt(s+rad))*mp.exp(1j*alpha*s),[1-rad,4-rad,9-rad])
   assert abs(left-right)<mp.mpf('1e-50')
   comparisons+=1
base=Path(__file__).resolve().parent
pr=base/'NORMAL-SUBSTITUTION-PRIMARY' if (base/'NORMAL-SUBSTITUTION-PRIMARY').exists() else base/'PRIMARY'
meta=json.loads((pr/'PRIMARY-SOURCES.json').read_text())
for n,r in meta.items():
 z=(pr/n).read_bytes();assert hashlib.sha256(z).hexdigest()==r['sha256'];assert hashlib.sha1(b'blob '+str(len(z)).encode()+b'\0'+z).hexdigest()==r['git_blob']
print(json.dumps({'exact_original_normal_identities':2,'exact_source_to_level_interval_bounds':bounds,'independent_complex_phase_integral_comparisons':comparisons,'precision_decimal_digits':60,'verified_primary_blobs':len(meta),'local_lean':'NOT_RUN','full_ambient_fourier_identity':'NEXT_JOIN'},indent=2))
