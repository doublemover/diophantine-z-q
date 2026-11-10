#!/usr/bin/env python3
"""Exact Gaussian-integer finite checks, not Lean/kernel acceptance."""
from pathlib import Path
import json,math
H=Path(__file__).resolve().parent;O=H.parent/'forward-canonical-cm-count-r2'
i=json.loads((O/'intake.json').read_text())
for n in i['order']:assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n

def add(z,w):return z[0]+w[0],z[1]+w[1]
def mul(z,w):return z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0]
def chi(p,x):
 x=pow(x%p,(p-1)//2,p)
 return -1 if x==p-1 else x
samples=[];values=0;fibers=0
for p in range(5,600):
 if p%4!=1 or any(p%d==0 for d in range(2,math.isqrt(p)+1)):continue
 g=next(g for g in range(2,p) if len({pow(g,k,p) for k in range(p-1)})==p-1)
 psi={0:(0,0)}
 for k in range(p-1):psi[pow(g,k,p)]=[(1,0),(0,1),(-1,0),(0,-1)][k%4]
 for x in range(p):
  assert mul(psi[x],psi[x])==(chi(p,x),0)
  assert psi[x*x%p]==(chi(p,x),0)
  assert sum(1 for y in range(p) if y*y%p==x)==1+chi(p,x)
  values+=1;fibers+=1
 J=(0,0)
 for x in range(p):J=add(J,mul(psi[x],(chi(p,1-x),0)))
 # Weighted square fibers give the exact cubic trace/Jacobi comparison.
 S=sum(chi(p,x*x*x-x) for x in range(p))
 assert S==2*J[0]
 assert J[0]*J[0]+J[1]*J[1]==p
 count=p+1+S
 assert count%4==0 and J[0]%2==1 and J[1]%2==0
 for a in range(-math.isqrt(p),math.isqrt(p)+1):
  for b in range(-math.isqrt(p),math.isqrt(p)+1):
   if a*a+b*b==p and a%2 and b%2==0:assert S*S==4*a*a
 samples.append((p,g,J,S,count))
# Wrong Frobenius sign is detected; our S is #E-p-1, not p+1-#E.
assert samples[0][0]==5 and samples[0][3]==2 and samples[0][4]==8
print(json.dumps({'unchanged_r2_sources':len(i['order']),'prime_fields':len(samples),
 'quartic_values':values,'square_fibers':fibers,'first_samples':samples[:8],
 'complete_symbolic_route':'DRAFT','Lean_run':False},indent=2))
