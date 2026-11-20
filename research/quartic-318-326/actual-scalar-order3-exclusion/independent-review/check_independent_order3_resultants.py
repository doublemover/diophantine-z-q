from fractions import Fraction as F
from math import gcd,prod
from itertools import permutations
import json,sys
from hashlib import sha256
from pathlib import Path
P=Path(sys.argv[1])
raw=P.read_bytes()
assert sha256(raw).hexdigest()=='1f7305f23e734423b129af730dad0469c224146acacd2c4ea50e065c7493bc16'
ref=json.loads(raw)
R=4376874610839020
b=204618888056724185
A=17*144*b
O=(F(0),F(0)); I=(F(1),F(0))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def sc(n,a):return (n*a[0],n*a[1])
def mul(a,b):return (a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def norm(a):return a[0]**2-2*a[1]**2
def inv(a):return sc(1/norm(a),(a[0],-a[1]))
def poly_mul(a,b):
 c=[O]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=add(c[i+j],mul(x,y))
 return c
d=(F(3),F(-1)); ds=mul(d,d); d4=mul(ds,ds)
# f_d(N) coeffs ascending, use Newton sums rather than elimination determinants.
f=[add(add((F(3),F(0)),sc(-6*R**2*k2,ds)),sc(-R**4*k4,d4)) if j==0 else add(sc(-6*R**2*k2,ds),sc(-R**4*k4,d4)) for j,(k2,k4) in enumerate(zip([1,-2,1,0,0],[1,-4,6,-4,1]))]
c=[mul(x,inv(f[-1])) for x in f]
assert c[-1]==I
conj=[(x,-y) for x,y in c]
one=poly_mul(c,conj)
assert all(y==0 for x,y in one)
powers=[O]
for k in range(1,17):
 acc=O
 for j in range(1,min(k-1,4)+1):acc=add(acc,mul(c[4-j],powers[k-j]))
 if k<=4:acc=add(acc,sc(k,c[4-k]))
 powers.append(sc(-1,acc))
S=[None]+[norm(a) for a in powers[1:]]
e=[F(1)]
for k in range(1,17):
 e.append(-sum(e[j]*S[k-j] for j in range(k))/k)
g=poly_mul(one,[(x,F(0)) for x in e[::-1]])
coeff=list(map(int,ref['eliminant_coefficients']))
assert g==[(F(x,coeff[0]),F(0)) for x in coeff[::-1]]
print('Independent Newton-sum reconstruction of exact 24-degree eliminant')
def det4(m):
 return sum((-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))*prod(m[i][p[i]] for i in range(4)) for p in permutations(range(4)))
fixed=2*3*7*R*(1+A)*b
# Replicate only target value, via multiplication determinant mod N^4-q, no resultant library.
for label,k,n in [('H',144*b,(1+A)**2),('Lprime',7056*b,48*(1+A)**2)]:
 q=F(n,k); m=[[F(0)]*4 for _ in range(4)]
 for j in range(4):
  for e,x in enumerate(coeff[::-1]):
   power,row=divmod(e+j,4); m[row][j]+=x*q**power
 z=abs(det4(m)*k**24)
 assert z.denominator==1
 z=z.numerator
 strip=z//gcd(z,pow(fixed,z.bit_length(),z))
 assert strip==int(ref['resultants'][label]['exact_moving_resultant'])
 print(label,strip.bit_length(),'bits matched by independent norm determinant')
