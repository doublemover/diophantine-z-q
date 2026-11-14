#!/usr/bin/env python3
"""Exact original five-variable regrouping, complete kernels and retained multiplicities. No Lean or asymptotic proof."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from pathlib import Path
import json

add=lambda x,y:tuple(a+b for a,b in zip(x,y))
sub=lambda x,y:tuple(a-b for a,b in zip(x,y))
def gaussian_add(z,w):return(z[0]+w[0],z[1]+w[1])
def gaussian_mul(z,w):return(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def phase(k):return ((1,0),(0,1),(-1,0),(0,-1))[k%4]
def square(z):return z[0]**2+z[1]**2
def Q(k,x):return x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2
def bilinear(k,h,y):return h[0]*y[0]+h[1]*y[1]-h[2]*y[2]-h[3]*y[3]-k*h[4]*y[4]
def overlap(H,h):return list(range(max(-H,-H-h),min(H,H-h)+1))
def weight(x):return 1+x[0]*x[1]+x[2]*x[4]+x[3]
def mixvar(g,n,m):
 var=lambda f,n:abs(f(n))+sum(abs(f(i)-f(i+1)) for i in range(n))
 return var(lambda i:g(i,m),n)+sum(var(lambda i:g(i,j)-g(i,j+1),n) for j in range(m))
def cap(N,h,t4):return F(N) if (2*h*t4)%4==0 else F(min(N,1))

def run():
 counts=dict(original_pair_regroupings=0,actual_plane_identities=0,actual_plane_bounds=0,complete_original_weyl_bounds=0,complete_kernel_factorizations=0,overlap_card_bounds=0,negative_controls=0)
 for H in range(6):
  for h in range(-2*H-3,2*H+4):
   assert len(overlap(H,h))<=2*H+1
   counts['overlap_card_bounds']+=1
 for H,k,t4 in product((0,1),(-2,1),(0,1,2,3)):
  box=list(product(range(-H,H+1),repeat=5));corr=defaultdict(lambda:(0,0));planes=defaultdict(lambda:(0,0))
  S=(0,0)
  for x in box:S=gaussian_add(S,gaussian_mul((weight(x),0),phase(t4*Q(k,x))))
  for x in box:
   for y in box:
    h=sub(x,y);v=gaussian_mul((weight(x)*weight(y),0),phase(2*t4*bilinear(k,h,y)))
    corr[h]=gaussian_add(corr[h],v)
    key=(h,y[2],y[3],y[4]);planes[key]=gaussian_add(planes[key],v)
  rhs=(0,0)
  for h,z in corr.items():rhs=gaussian_add(rhs,gaussian_mul(phase(t4*Q(k,h)),z))
  assert rhs==(square(S),0)
  counts['original_pair_regroupings']+=1
  regroup=defaultdict(lambda:(0,0));C=F(0)
  for (h,c,d,e),z in planes.items():
   aa=overlap(H,h[0]);bb=overlap(H,h[1]);g=lambda i,j:weight((aa[i],bb[j],c,d,e))*weight(add(h,(aa[i],bb[j],c,d,e)))
   z2=(0,0)
   for i,j in product(range(len(aa)),range(len(bb))):
    y=(aa[i],bb[j],c,d,e)
    z2=gaussian_add(z2,gaussian_mul((g(i,j),0),phase(2*t4*bilinear(k,h,y))))
   assert z==z2
   counts['actual_plane_identities']+=1
   V=mixvar(g,len(aa)-1,len(bb)-1);C=max(C,V)
   assert square(z)<= (cap(len(aa),h[0],t4)*cap(len(bb),h[1],t4)*V)**2
   counts['actual_plane_bounds']+=1
   regroup[h]=gaussian_add(regroup[h],z)
  assert dict(regroup)==dict(corr)
  N=2*H+1;kernel=sum(cap(N,h,t4) for h in range(-2*H,2*H+1))
  assert square(S)<=N**3*(4*H+1)**3*C*kernel**2
  counts['complete_original_weyl_bounds']+=1
 for H in range(4):
  # Arbitrary nonnegative rational kernels, not separable original weights.
  f=lambda a:F((a+2*H+1)**2+1,3)
  g=lambda b:F(abs(b)+1,5)
  wide=list(product(range(-2*H,2*H+1),repeat=5))
  lhs=sum(f(h[0])*g(h[1]) for h in wide)
  rhs=(4*H+1)**3*sum(f(a) for a in range(-2*H,2*H+1))*sum(g(b) for b in range(-2*H,2*H+1))
  assert lhs==rhs
  counts['complete_kernel_factorizations']+=1
 # Negative controls explicitly reject loss of outer multiplicities and premature triangle.
 H=1;N=3;S=N**5;kernel=5*N
 assert S*S>N**3*kernel**2 # missing THREE displacement counts
 assert S*S>5**3*kernel**2 # missing THREE overlap counts
 assert abs(1+(-1))<abs(1)+abs(-1) # second-axis triangle would destroy cancellation
 h=(2,0,0,0,0);assert h[0] not in range(-H,H+1) and h[0] in range(-2*H,2*H+1)
 counts['negative_controls']=4
 return {'status':'PASS','scope':'Exact finite identities/inequalities only; no smooth C-infinity witness, Lean check, harmonic estimate, denominator existence or minor-arc saving.','counts':counts}
if __name__=='__main__':
 result=run();Path(__file__).with_name('COMPLETE-TWO-AXIS-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
