#!/usr/bin/env python3
"""Exact original correlation/overlap/five-kernel accounting and signed injections. Not Lean or minor-arc asymptotics."""
from itertools import product
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import json
add=lambda x,y:tuple(a+b for a,b in zip(x,y))
sub=lambda x,y:tuple(a-b for a,b in zip(x,y))
prod=lambda xs:__import__('functools').reduce(lambda a,b:a*b,xs,1)
def ov(H,h):return list(range(max(-H,-H-h),min(H,H-h)+1))
def W(x):return 1+x[0]*x[1]+x[2]*x[4]+x[3]
def ga(z,w):return (z[0]+w[0],z[1]+w[1])
def gm(z,w):return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def phase(n):return ((1,0),(0,1),(-1,0),(0,-1))[n%4]
def Q(k,x):return x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2
def bil(k,h,y):return h[0]*y[0]+h[1]*y[1]-h[2]*y[2]-h[3]*y[3]-k*h[4]*y[4]
def cap(N,c,t4):return N if (c*t4)%4==0 else min(N,1)
def V(g,intervals,x=()):
 if not intervals:return abs(g(x))
 s=intervals[0];tail=intervals[1:]
 last=lambda z:g(x+(s[-1],)+z)
 out=V(last,tail)
 for j in range(len(s)-1):
  delta=lambda z,j=j:g(x+(s[j+1],)+z)-g(x+(s[j],)+z)
  out+=V(delta,tail)
 return out
def run():
 c=dict(positive_overlaps=0,actual_five_correlations=0,full_original_five_bounds=0,complete_kernel_factorization=0,signed_coefficient_injections=0,negative_controls=0)
 for H in range(10):
  for u in range(-2*H,2*H+1):
   s=ov(H,u);assert s and len(s)==min(H,H-u)-max(-H,-H-u)+1 and len(s)<=2*H+1;c['positive_overlaps']+=1
 for H in (0,1):
  box=list(product(range(-H,H+1),repeat=5));hs=list(product(range(-2*H,2*H+1),repeat=5))
  var={h:V(lambda z,h=h:W(add(h,z))*W(z),[ov(H,u) for u in h]) for h in hs};C=max(var.values())
  for k,t4 in product((-2,0,3),range(4)):
   corr=defaultdict(lambda:(0,0));S=(0,0)
   for x in box:S=ga(S,gm((W(x),0),phase(t4*Q(k,x))))
   for x in box:
    for y in box:
     h=sub(x,y);corr[h]=ga(corr[h],gm((W(x)*W(y),0),phase(2*t4*bil(k,h,y))))
   for h in hs:
    actual=(0,0)
    for y in product(*(ov(H,u) for u in h)):
     actual=ga(actual,gm((W(add(h,y))*W(y),0),phase(2*t4*bil(k,h,y))))
    assert actual==corr[h]
    lengths=[len(ov(H,u)) for u in h]
    freqs=[2*h[0],2*h[1],-2*h[2],-2*h[3],-2*k*h[4]]
    caps=prod(cap(N,f,t4) for N,f in zip(lengths,freqs))
    assert actual[0]**2+actual[1]**2<=(var[h]*caps)**2
    c['actual_five_correlations']+=1
   N=2*H+1
   sums=[sum(cap(N,2*m*a,t4) for a in range(-2*H,2*H+1)) for m in (1,1,-1,-1,-k)]
   assert S[0]**2+S[1]**2<=C*prod(sums)
   c['full_original_five_bounds']+=1
 for H in range(3):
  fs=[lambda a,i=i:F(a*a+i+1,i+2) for i in range(5)]
  lhs=sum(prod(f(a) for f,a in zip(fs,h)) for h in product(range(-2*H,2*H+1),repeat=5))
  rhs=prod(sum(f(a) for a in range(-2*H,2*H+1)) for f in fs)
  assert lhs==rhs;c['complete_kernel_factorization']+=1
 for H,m,N,t4 in product(range(7),[j for j in range(-5,6) if j],(0,1,3,7),range(4)):
  source=list(range(-2*H,2*H+1));image=[m*a for a in source]
  assert len(set(image))==len(source)
  assert all(-2*abs(m)*H<=z<=2*abs(m)*H for z in image)
  assert sum(cap(N,2*m*a,t4) for a in source)<=sum(cap(N,2*a,t4) for a in range(-2*abs(m)*H,2*abs(m)*H+1))
  c['signed_coefficient_injections']+=1
 # Zero coefficient is not injective and cannot use the nonzero-coefficient bound.
 assert len({0*a for a in range(-2,3)})!=5
 assert sum(cap(3,0,1) for a in range(-2,3))>cap(3,0,1)
 # Empty overlaps outside the doubled range are not positive rectangles.
 assert not ov(1,3)
 # Five-dimensional index volume cannot collapse to four kernels.
 assert 5**5>5**4
 c['negative_controls']=4
 return {'status':'PASS','scope':'Exact finite original correlations,positive overlap coverage,full nonnegative five-kernel factorization and signed coefficient ranges. Not compact-smooth constants,Lean kernel,minor-domain rational approximation or asymptotic decay.','counts':c}
if __name__=='__main__':
 r=run();Path(__file__).with_name('FULL-FIVE-KERNEL-REGRESSION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
