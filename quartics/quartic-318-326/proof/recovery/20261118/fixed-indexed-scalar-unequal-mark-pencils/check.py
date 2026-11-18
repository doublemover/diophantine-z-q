"""Arithmetic controls for the paper proof; no third-party dependencies."""
from fractions import Fraction as F
from math import isqrt
import json
b=204618888056724185
def data(beta,x):
 h=1-beta*(x*x+108);k=F(12,h);c=1+3*beta*k*k
 A=F(1+beta*(x*x+108),h);L=F(2*x,h)
 assert c==A*A-beta*L*L and 0<beta*k*k<1
 return h,k,c
def prime(p): return p>1 and all(p%i for i in range(2,isqrt(p)+1))
def ch(a,p):return pow(a%p,(p-1)//2,p) if a%p else 0
def val(n,p):
 if not n:raise AssertionError
 e=0
 while n%p==0:n//=p;e+=1
 return e
checks=0
for beta in (17,65,89,b):
 for x in range(-48,49,6):
  h,k,c=data(beta,x)
  for s in (F(-3,7),F(1,2),F(2),F(4,9)):
   u=(s-3*beta*k)/(1+k*s)
   e=lambda t:(t*t-beta)/(t*t+3*beta)
   Y=lambda t:4*beta*t/(t*t+3*beta)
   assert Y(s)**2==beta*(1-e(s))*(1+3*e(s)) and Y(u)**2==beta*(1-e(u))*(1+3*e(u))
   assert (u*u+3*beta)*(1+k*s)**2==c*(s*s+3*beta)
   q2=(s-3*beta*k)**2-beta*(1+k*s)**2
   assert e(s)*e(u)*((s*s+3*beta)*c)**2==c*(s*s-beta)*q2
   checks+=1
# Count singular-reduction residual tests independently for every unit nonsquare.
cases=0
for p in range(5,115):
 if not prime(p):continue
 for beta in range(1,p):
  if ch(beta,p)!=p-1:continue
  for k in range(1,p):
   if (1+3*beta*k*k)%p:continue
   a=pow(k,-1,p);assert (a*a+3*beta)%p==0
   for target in (1,p-1):
    assert any((1+k*s)%p and ch(s*s-beta,p)==target for s in range(p))
    cases+=1
h,k,c=data(b,54);p=31
assert b%p==2 and val(c.numerator,p)==1 and c.denominator%p and 28%p
for s in (0,None):
 if s is None:q=1-b*k*k
 else:q=(-b)*((3*b*k)**2-b)
 assert q.numerator%p and q.denominator%p
print(json.dumps(dict(index=328655617654071015360,beta=b,D_mod_31=28,x=54,h=h,k=str(k),c=str(c),c_valuation_31=1,matching_identity_checks=checks,singular_reduction_checks=cases),indent=2))
