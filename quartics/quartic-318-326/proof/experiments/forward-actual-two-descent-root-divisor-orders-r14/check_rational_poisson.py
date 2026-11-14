"""Exact original residue parametrization and finite rational-arc regression.
No Lean execution. Numerical quadrature/truncation is not a certified proof.
"""
import math,cmath,itertools,json
from pathlib import Path
from fractions import Fraction
count=0
for q in range(1,8):
 seen=set()
 for x in itertools.product(range(-2,3),repeat=5):
  r=tuple(t%q for t in x);z=tuple(t//q for t in x)
  assert tuple(a+q*b for a,b in zip(r,z))==x
  assert (r,z) not in seen;seen.add((r,z))
  for k in [318,326]:
   Q=lambda v:v[0]**2+v[1]**2-v[2]**2-v[3]**2-k*v[4]**2
   assert Fraction(3*(Q(x)-Q(r)),q).denominator==1
  count+=1
N=16384;M=64;radius=.8;step=2*radius/N

def bump(x):return math.exp(-1/(1-(x/radius)**2)) if abs(x)<radius else 0

def dual(k,a,q,beta,B):
 ans=complex((B/q)**5)
 for sign in [1,1,-1,-1,-k]:
  val=0j
  for j in range(N):
   y=-radius+(j+.5)*step;char_sum=0j
   for r in range(q):
    t=(r-B*y)/q;den=math.sin(math.pi*t)
    D=(2*M+1) if abs(den)<1e-13 else math.sin((2*M+1)*math.pi*t)/den
    char_sum+=cmath.exp(2j*math.pi*a*sign*r*r/q)*D
   val+=bump(y)*cmath.exp(2j*math.pi*beta*B*B*sign*y*y)*char_sum
  ans*=val*step
 return ans

def primal(k,a,q,beta,B):
 ans=1+0j
 for sign in [1,1,-1,-1,-k]:
  ans*=sum(bump(z/B)*cmath.exp(2j*math.pi*(a/q+beta)*sign*z*z) for z in range(-30,31))
 return ans
rows=[]
for k,a,q,beta,B in [(318,1,2,.001,3.),(326,2,3,-.002,2.),(318,1,1,0.,2.)]:
 p=primal(k,a,q,beta,B);d=dual(k,a,q,beta,B);err=abs(p-d);assert err<3e-7,err
 rows.append(dict(kappa=k,a=a,q=q,beta=beta,B=B,primal=[p.real,p.imag],finite_dual=[d.real,d.imag],absolute_error=err))
out={'status':'PASS','exact_integer_bijection_and_phase_cases':count,'numerical_cases':rows,'frequency_box':M,'quadrature_steps':N,'scope':'Exact original integer residue decomposition and phase congruences; finite numerical full rational-arc Poisson. No certified truncation or Lean execution. Infinite sums and identities require the source proof and hosted validation.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
