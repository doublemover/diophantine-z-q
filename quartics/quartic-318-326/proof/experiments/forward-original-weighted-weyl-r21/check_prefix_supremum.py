from fractions import Fraction as F
from math import gcd
from collections import defaultdict
import json
counts=defaultdict(int)
# Exact Gaussian characters at t=k/4, all positive and signed coefficients.
roots=[1+0j,1j,-1+0j,-1j]
for H in range(5):
 for lo in range(-H,H+2):
  for hi in range(lo-1,H+1):
   for c in [-3,-1,1,2,5]:
    for k in range(4):
     s=list(range(lo,hi+1));ph=lambda x:roots[(k*c*x*x)%4]
     z=sum(map(ph,s));rhs=0
     for h in range(-2*H,2*H+1):
      ov=[y for y in s if h+y in s]
      assert ov==list(range(max(lo,lo-h),min(hi,hi-h)+1))
      n=max(0,min(hi,hi-h)-max(lo,lo-h)+1)
      assert n<=2*H+1
      co=sum(ph(h+y)*ph(y).conjugate() for y in ov)
      lin=roots[(k*c*h*h)%4]*sum(roots[(k*2*c*h*y)%4] for y in ov)
      assert co==lin
      rhs+=co;counts['overlap_phase_and_length']+=1
     assert z*z.conjugate()==rhs;counts['complete_interval_difference']+=1
# Exact algebra with log replaced by arbitrary monotone nonnegative Lq<=LQ.
for K in range(6):
 for L in range(1,7):
  for n in range(1,5):
   for q in range(n,8):
    for Q in range(q,9):
     lq,lQ=F(q,10),F(Q,10)
     lhs=(16*F(K,q)+2)*(2*L+2*q*(1+lq))
     expanded=32*F(K*L,q)+32*K*(1+lq)+4*L+4*q*(1+lq)
     upper=32*F(K*L,n)+32*K*(1+lQ)+4*L+4*Q*(1+lQ)
     assert lhs==expanded and lhs<=upper;counts['expanded_uniform_budget']+=1
for H in range(7):
 for c in [-7,-2,-1,1,2,7]:
  images=[c*h for h in range(-2*H,2*H+1)]
  assert len(images)==len(set(images)) and all(-2*abs(c)*H<=x<=2*abs(c)*H for x in images)
  counts['signed_kernel_injection']+=1
# Exact canonical minor approximation exclusion is reused and separately
# exercised here on rational points with fully reduced q witnesses.
for N in [1,2,3]:
 B=(N+1)**3;Q=(B*B+N-1)//N;r=F(N,B*B)
 for t in [F(j,31) for j in range(1,31)]:
  major=any(F(a,q)-r<t<=F(a,q)+r for q in range(1,N+1) for a in range(q) if gcd(a,q)==1)
  if not (-r<t<=1-r) or major:continue
  candidates=[(a,q) for q in range(1,min(Q,32)+1) for a in range(q+1) if gcd(a,q)==1 and abs(t-F(a,q))<=F(1,(Q+1)*q)]
  assert candidates
  assert all(N<q<=Q and abs(t-F(a,q))<=F(1,q*q) for a,q in candidates)
  counts['actual_minor_witness']+=1
# Negative controls: intervals cannot be replaced by subsets, c=0 cannot
# be injected, a single zero displacement does not equal the full square,
# and omitting q-log mixed term breaks exact expansion.
assert [0,2]!=list(range(0,3))
assert len(set(0*h for h in range(-2,3)))<5
assert abs(sum(roots[(0*x*x)%4] for x in [-1,0,1]))**2!=3
K=L=q=1;lq=F(1,10)
assert (16*F(K,q)+2)*(2*L+2*q*(1+lq)) != 32*F(K*L,q)+4*L+4*q*(1+lq)
counts['negative_controls']=4
print(json.dumps({'status':'PASS','checks':dict(counts),'scope':'Exact finite combinatorics, Gaussian characters, rational range algebra. Not Lean or numerical/asymptotic integration.'},indent=2))
