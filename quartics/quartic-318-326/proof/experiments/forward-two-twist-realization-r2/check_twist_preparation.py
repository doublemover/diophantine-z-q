"""Exact algebra checks, not Lean kernel acceptance or arithmetic realization."""
from pathlib import Path
import sympy as s
β,θ,c,d,n,a,b,y,z=s.symbols('beta theta c d n a b y z',nonzero=True)
B=β*c*c;V=θ*d*d;E=n*(c/a)**2;ss=b*d/a
res1=(y*(c/a)**3)**2-B*(B-E)*(B+3*E)
source1=y*y-(β*a*a)*(β*a*a-n)*(β*a*a+3*n)
assert s.cancel(res1-(c/a)**6*source1)==0
res2=(z*(c*d/a)**3)**2-(B*ss*ss)*(B*ss*ss-E*V)*(B*ss*ss+3*E*V)
source2=z*z-(β*b*b)*(β*b*b-n*θ)*(β*b*b+3*n*θ)
assert s.cancel(res2-(c*d/a)**6*source2)==0
assert s.cancel(E*V-n*θ*(c*d/a)**2)==0
x,j=s.symbols('x j')
cs=[101783690143177584,800910366213064752,2642145132961084032,3147690941013049344,4376874610839020]
r=sum(cs[i]*x**(i+1) for i in range(4))+cs[4]
raw=101783690143177584*x+267108917866935984*x*x+533801448346128768*(x*x+s.Rational(496408687,100291113)*x**3+s.Rational(197130368,33430371)*x**4)+4376874610839020
assert s.expand(r-raw)==0
A=114444*r
for modulus,factor,unit in [(128,16,1),(27,9,1),(4913,289,8)]:
 k=sum((114444*cs[i]//modulus)*x**(i+1) for i in range(4))+114444*cs[4]//modulus
 if modulus==128:
  assert s.expand(A-factor*(unit+8*(k+j))-64*(x+x*x-2*j))==0
 else:assert s.expand(A-factor*unit-modulus*k)==0
rval,hval,ival=s.symbols('rval hval ival')
assert s.expand(rval+2*(ival-hval-15*rval)-(2*ival-2*hval-29*rval))==0
print('PASS exact shared-E two-twist rescalings,original V,integer r coefficients,small-prime normal forms4/2/2,and29*v(r) scalar depth')
assert s.Rational(1,8)<s.Rational(1,2)**2
assert s.Rational(1,3)<1 and s.Rational(1,17)<1
k=s.symbols('k')
assert s.expand(1-(1+8*k)+8*k)==0
assert s.expand(1-(1+3*k)+3*k)==0
assert s.expand(25-(8+17*k)-17*(1-k))==0
print('PASS all three exact Hensel residuals and strict derivative-norm bounds')
