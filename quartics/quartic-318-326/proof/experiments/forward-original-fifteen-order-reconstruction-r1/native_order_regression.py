from pathlib import Path
from fractions import Fraction as F
from math import isqrt,gcd
import re,json
root=Path(__file__).parent
add=lambda x,y:(x[0]+y[0],x[1]+y[1])
neg=lambda x:(-x[0],-x[1])
sub=lambda x,y:add(x,neg(y))
mul=lambda x,y:(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
scale=lambda n,x:(n*x[0],n*x[1])
def inv(x):
 n=x[0]*x[0]-2*x[1]*x[1]
 assert n
 return x[0]/n,-x[1]/n
sq=lambda x:mul(x,x)
D=(F(11),F(-6))
x,y=(F(1),F(1)),(F(0),F(2))
data=json.loads((root/'exact-doubling-fractions.json').read_text())
for n in [2,4,8,16]:
 m=mul(sub(scale(3,sq(x)),D),inv(scale(2,y)))
 X=sub(sq(m),scale(2,x));Y=sub(mul(m,sub(x,X)),y)
 assert sq(Y)==sub(mul(sq(X),X),mul(D,X))
 row=data[str(n)]
 assert [str(t) for t in X]==row['x'] and [str(t) for t in Y]==row['y']
 assert [str(t) for t in m]==row['slope']
 assert str(X[0].denominator*X[1].denominator)==row['denominator']
 x,y=X,Y
for name,src,key,n in [('x8','ConcreteOriginalFourEightCoordinates318','x',8),('y8','ConcreteOriginalFourEightCoordinates318','y',8),('slope8','ConcreteOriginalFourEightCoordinates318','slope',8),('x16','ConcreteOriginalSixteenDenominator318','x',16),('slope16','ConcreteOriginalSixteenDenominator318','slope',16)]:
 text=(root/(src+'.lean')).read_text()
 m=re.search(r'def '+name+r' : K := pair \(([^)]+)\) \(([^)]+)\)',text)
 assert m and [str(F(t)) for t in m.groups()]==data[str(n)][key]
D16=int(data['16']['denominator']);assert D16%9649==7229
prime=lambda p:p>=2 and all(p%d for d in range(2,isqrt(p)+1))
assert all(prime(p) for p in [9649,2441,149])
assert 57**2+80**2==9649 and (57%16,80%16,57%7,80%7)==(9,0,1,3)
assert pow(1743,8,9649)==9648 and pow(1075,4,9649)==2
roots=[r for r in range(9649) if r*r%9649==2]
def count(r):
 p=9649;c=(3-r)**2%p;n=1
 for x in range(p):
  y=(x*x*x-c*x)%p
  n+=1 if y==0 else (2 if pow(y,(p-1)//2,p)==1 else 0)
 return n
counts=[count(r) for r in roots]
assert sorted(counts)==[9536,9764]
assert 9764//4==2441 and 9536//4==2384 and 2384//149==16
assert gcd(2441,2384)==1
# This does not compute the opposite native quotient order: all five possibilities remain.
possible=[n for n in range(1,2385) if 2384%n==0 and n%149==0]
assert possible==[149,298,596,1192,2384]
# Negative controls: full count is not quarter; divisibility does not force equality.
assert 2441!=9764 and 149!=2384 and 298%149==0
print(json.dumps({'exact_doublings':4,'source_coordinate_pairs':5,'prime_certificates':3,'actual_finite_curve_counts':counts,'native_opposite_order_candidates_not_computed':possible,'D16_mod_9649':D16%9649,'negative_controls':3},sort_keys=True))
