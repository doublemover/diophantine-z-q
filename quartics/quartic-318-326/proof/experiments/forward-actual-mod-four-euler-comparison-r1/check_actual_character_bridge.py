#!/usr/bin/env python3
import itertools,json,math,hashlib
from fractions import Fraction as F
from pathlib import Path
import sympy as s
import mpmath as m
m.mp.dps=90
c=dict(mod_four_multiplicativity=0,original_quadratic_signs=0,actual_local_decompositions=0,actual_full_euler_identities=0,positive_correction_products=0,actual_character_boundary_samples=0,actual_complex_euler_factors=0)
chi=lambda n:0 if n%2==0 else (1 if n%4==1 else -1)
for a,b in itertools.product(range(-30,31),repeat=2):
 assert chi(a*b)==chi(a)*chi(b);c['mod_four_multiplicativity']+=1
for p in s.primerange(3,1500):
 leg=int(s.legendre_symbol(-1,p));assert leg==chi(p);c['original_quadratic_signs']+=1
def density(p,k):
 e=chi(p);v0=p+(p-1)*e
 return F((p-1)*(p-e)*(2*v0+(k-2)*(p-e))+v0*v0-1,p**4-1)
for kap,gs in [(1,[0,-1]),(318,[0,-318,1]),(326,[0,-326,1]),(3,[0,-3,2,5])]:
 k=len(gs);exception=2*abs(kap)*math.prod(abs(gs[i]-gs[j]) for i in range(k) for j in range(i+1,k))
 for N in [1,2,64,80,105,125,200,500]:
  ps=[int(p) for p in s.primerange(16*(k+2),N) if exception%p]
  g={p:density(p,k) for p in ps}
  corr={p:(1-g[p])/((1-F(1,p))**k*(1-F(chi(p),p))**2) for p in ps}
  for p in ps:
   assert 1-g[p]==corr[p]*(1-F(1,p))**k*(1-F(chi(p),p))**2 and corr[p]>0
   c['actual_local_decompositions']+=1
  full=math.prod(F(1)/(1-g[p]) for p in ps);C=math.prod(corr.values())
  ordinary=math.prod(F(1)/(1-F(1,p)) for p in ps)
  character=math.prod(F(1)/(1-F(chi(p),p)) for p in ps)
  assert full==ordinary**k*character**2/C;c['actual_full_euler_identities']+=1
  assert C>0;c['positive_correction_products']+=1
L1=m.pi/4
for sig in [m.mpf(1)+m.mpf(i)/1000 for i in range(-50,51)]:
 L=m.dirichlet(sig,[0,1,0,-1]);assert L1/2<L<2*L1;c['actual_character_boundary_samples']+=1
for sig in [m.mpf('1.01'),m.mpf('1.1'),m.mpf('1.5'),m.mpf(2)]:
 for p in s.primerange(2,200):
  original=0 if p==2 else int(s.legendre_symbol(-1,p))
  lhs=1/(1-m.mpc(original)*m.mpc(int(p))**(-m.mpc(sig)))
  rhs=1/(1-m.mpf(chi(p))*m.mpf(int(p))**(-sig))
  assert abs(lhs-rhs)<m.mpf('1e-80');c['actual_complex_euler_factors']+=1
# Verify official pinned primary source bytes against Git tree object ids.
r=Path(__file__).resolve().parent
manifest=json.loads((r/'PINNED-PRIMARY.json').read_text())
paths=manifest['files']
for name,record in paths.items():
 b=(r/name).read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==record['git_blob'],name
print(json.dumps({'status':'PASS','checks':c,'pinned_primary_blobs_verified':len(paths),'precision_digits':90,'scope':'Exact original mod-four sign and Euler decompositions; numerical boundary sanity checks do not replace pinned proven L-function nonvanishing/continuity. No sigma=1 prime-product limit or Mertens growth claimed.'},sort_keys=True))
