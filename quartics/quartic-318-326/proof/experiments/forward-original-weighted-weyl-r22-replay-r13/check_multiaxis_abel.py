#!/usr/bin/env python3
"""Exact nonseparable multiaxis Abel/phase regression, not compact-smooth or Lean validation."""
from itertools import product
from pathlib import Path
import json
add=lambda x,y:tuple(a+b for a,b in zip(x,y))
scale=lambda n,u:tuple(n*a for a in u)
def poly(x):return 2+sum(x)+sum(x[i]*x[j] for i in range(len(x)) for j in range(i))+prod(x)
def prod(xs):
 z=1
 for x in xs:z*=x
 return z
def rect(g,axes,x):
 if not axes:return g(x)
 u,N,s=axes[0]
 return sum(rect(g,axes[1:],add(x,scale(j,u)))*s**j for j in range(N+1))
def variation_terms(g,axes,x):
 if not axes:return [abs(g(x))]
 u,N,s=axes[0];tail=axes[1:]
 out=variation_terms(g,tail,add(x,scale(N,u)))
 delta=lambda z:g(add(z,u))-g(z)
 for j in range(N):out+=variation_terms(delta,tail,add(x,scale(j,u)))
 return out
def cap(N,s):return max(abs(sum(s**j for j in range(n))) for n in range(N+2))
def ph(n):return ((1,0),(0,1),(-1,0),(0,-1))[n%4]
def gadd(z,w):return (z[0]+w[0],z[1]+w[1])
def gmul(z,w):return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def bilin(k,h,x):return h[0]*x[0]+h[1]*x[1]-h[2]*x[2]-h[3]*x[3]-k*h[4]*x[4]
def run():
 c=dict(multiaxis_abel_bounds=0,uniform_mixed_consumption=0,original_five_phase_identities=0,original_five_kernel_bounds=0,negative_controls=0)
 for d in range(6):
  dirs=[tuple(int(i==j) for i in range(d)) for j in range(d)]
  for ns,ss,x in product([tuple([0]*d),tuple([1]*d),tuple(i%3 for i in range(d))],list(product((-1,1),repeat=d)),[tuple([0]*d),tuple([-1]*d)]):
   axes=list(zip(dirs,ns,ss));g=poly
   terms=variation_terms(g,axes,x);V=sum(terms);C=max(terms,default=0);R=max(ns,default=0)
   caps=prod(cap(N,s) for u,N,s in axes)
   assert abs(rect(g,axes,x))<=caps*V
   assert V<=C*(1+R)**d
   assert abs(rect(g,axes,x))<=caps*C*(1+R)**d
   c['multiaxis_abel_bounds']+=1;c['uniform_mixed_consumption']+=1
 dirs=[tuple(int(i==j) for i in range(5)) for j in range(5)]
 for k,h,lo,ns,t4 in product((-2,0,3),[(0,0,0,0,0),(1,-1,2,1,-2)],[(0,0,0,0,0),(-1,1,0,-2,1)],[(0,0,0,0,0),(1,1,1,1,1),(2,1,0,1,2)],range(4)):
  g=lambda z:poly(add(z,h))*poly(z)
  freqs=[2*bilin(k,h,u) for u in dirs]
  ss=[1 if (f*t4)%4==0 else -1 for f in freqs]
  axes=list(zip(dirs,ns,ss));lhs=(0,0)
  for js in product(*(range(N+1) for N in ns)):
   y=add(lo,js);lhs=gadd(lhs,gmul((g(y),0),ph(2*t4*bilin(k,h,y))))
  rhs=gmul(ph(2*t4*bilin(k,h,lo)),(rect(g,axes,lo),0))
  assert lhs==rhs;c['original_five_phase_identities']+=1
  V=sum(variation_terms(g,axes,lo));caps=prod(cap(N,s) for u,N,s in axes)
  assert lhs[0]**2+lhs[1]**2<=(caps*V)**2;c['original_five_kernel_bounds']+=1
 # Mixed control is necessary, not just amplitude or first differences.
 g=lambda z:z[0]*z[1]
 assert g((1,1))-g((1,0))-g((0,1))+g((0,0))==1
 assert 2*bilin(3,(1,2,3,4,5),dirs[4])==-30
 assert 2*bilin(0,(1,2,3,4,5),dirs[4])==0 # degenerate fifth direction remains resonant
 assert cap(3,1)==4 and cap(3,-1)==1
 c['negative_controls']=4
 return {'status':'PASS','scope':'Exact finite nonseparable polynomial models and original five-frequency identities; not global compact-smooth bounds, Lean elaboration, displacement aggregation or minor decay.','counts':c}
if __name__=='__main__':
 r=run();Path(__file__).with_name('MULTIAXIS-ABEL-REGRESSION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
