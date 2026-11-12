"""Finite quadratic differencing and exact residue-kernel bounds. No Lean."""
import cmath,math,json
from pathlib import Path
correlations=0;bounds=0;kernels=0;maxerror=0.
for q in range(1,25):
 e=lambda x:cmath.exp(2j*math.pi*(x%q)/q)
 for c in range(q):
  kernel=[h for h in range(q) if 2*c*h%q==0]
  for b in range(q):
   G=sum(e(c*x*x+b*x) for x in range(q))
   rhs=q*sum(e(c*h*h+b*h) for h in kernel)
   err=abs(G*G.conjugate()-rhs);maxerror=max(maxerror,err)
   assert err<1e-9,(q,c,b,err)
   assert abs(G)**2<=q*len(kernel)+1e-9
   correlations+=1
for q in list(range(1,65))+[106,163,326,653,1024]:
 for k in [1,2,3,5,6,53,163,318,326,636,652]:
  K=[x for x in range(q) if k*x%q==0]
  quotients=[k*x//q for x in K]
  assert len(set(quotients))==len(K)
  assert all(0<=t<k for t in quotients)
  assert len(K)<=k
  kernels+=1
for q in list(range(1,25))+[53,106,163,326]:
 e=lambda x:cmath.exp(2j*math.pi*(x%q)/q)
 for a in [a for a in range(q) if math.gcd(a,q)==1][:8]:
  for k in [1,318,326]:
   for b in [0,1,q//2,q-1]:
    G=sum(e(a*k*x*x+b*x) for x in range(q))
    assert abs(G)**2<=q*2*k+1e-8,(q,a,k,b)
    bounds+=1
out={'status':'PASS','quadratic_correlation_cases':correlations,'exact_kernel_injection_cases':kernels,'unit_gauss_bound_cases':bounds,'max_finite_complex_roundoff':maxerror,'scope':'Finite numerical character identities and exact integer kernel injections, including even/composite/bad-prime/modulus1 cases. Infinite/general statements require source proof and hosted Lean; no local Lean execution.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
