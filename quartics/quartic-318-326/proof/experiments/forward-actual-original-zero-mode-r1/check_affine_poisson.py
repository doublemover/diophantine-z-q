"""Exact affine normalizations and finite numerical original residue regressions.
No Lean execution; numerical truncation is not certified.
"""
from fractions import Fraction as F
import cmath, math, json
from pathlib import Path
cases=0
for q in range(1,8):
 for B in [F(1,2),F(3),F(7,3)]:
  for r in range(-3,4):
   for m in range(-2,3):
    R=F(q)/B;c=F(r)/B
    assert (1/R)*m*c==F(m*r,q)
    assert 1/R**5==(B/q)**5
    for z in [-2,1]:
     assert c+R*z==(F(r)+q*z)/B
    cases+=1
N=16384;M=64;radius=.8;step=2*radius/N

def bump(x):
 return math.exp(-1/(1-(x/radius)**2)) if abs(x)<radius else 0

def finite_dual(k,beta,q,B,rs):
 out=complex((B/q)**5)
 for sign,r in zip([1,1,-1,-1,-k],rs):
  val=0j
  for j in range(N):
   y=-radius+(j+.5)*step;t=(r-B*y)/q
   den=math.sin(math.pi*t)
   kernel=(2*M+1) if abs(den)<1e-13 else math.sin((2*M+1)*math.pi*t)/den
   val+=bump(y)*cmath.exp(2j*math.pi*beta*B*B*sign*y*y)*kernel
  out*=val*step
 return out

def primal(k,beta,q,B,rs):
 out=1+0j
 for sign,r in zip([1,1,-1,-1,-k],rs):
  out*=sum(bump((r+q*z)/B)*cmath.exp(2j*math.pi*beta*sign*(r+q*z)**2) for z in range(-30,31))
 return out
rows=[]
for k,beta,q,B,rs in [(318,0.,2,3.,[1,0,1,0,1]),(318,.001,2,3.,[1,-1,0,1,0]),(326,-.002,3,2.,[1,0,-1,0,0])]:
 a=primal(k,beta,q,B,rs);b=finite_dual(k,beta,q,B,rs);err=abs(a-b)
 assert err<3e-7,err
 rows.append(dict(kappa=k,beta=beta,q=q,B=B,residue=rs,primal=[a.real,a.imag],finite_dual=[b.real,b.imag],absolute_error=err))
out={'status':'PASS','exact_normalization_cases':cases,'numerical_cases':rows,'frequency_box':M,'quadrature_steps':N,'scope':'Exact rational affine/Jacobian/phase identities plus finite numerical original residue Poisson checks. Numerical truncation is not certified; infinite summability and equality are source obligations. No Lean execution.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
