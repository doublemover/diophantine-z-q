from fractions import Fraction as Q
from math import gcd,isqrt
from itertools import product
from pathlib import Path
import json
from sympy import factorint
N=17*9145; a=Q(1297,532); Y=Q(149622419334526725,150568768);t,s=Q(48,691),Q(14,691)
assert (N*a*a)*(N*a*a-N)*(N*a*a+3*N)==Y**2 and 51*t*t+9145*s*s==4
w=17*t*s;b0=9145*w*w;B0=17*b0; V0=B0*B0*(1-b0/17);u=2-51*t*t
assert u*u==4-3*b0/17
E0=B0/a**2; s0=B0/a;y0=w**3*Y/a**3; z0=B0**4*b0*u/a**3
def test(b,E,s,y,z):
 B=17*b;V=B*B*(1-b/17); assert 0<b<17 and all([E,s,y,z]) and y*y==B*(B-E)*(B+3*E) and z*z==(B*s*s)*(B*s*s-E*V)*(B*s*s+3*E*V)
test(b0,E0,s0,y0,z0)
c=b0/17;d=1-c; M=32*3*17*5*31*59
def ord(p,x):
 a,b=abs(x.numerator),x.denominator;i=0; assert a
 while a%p==0:a//=p;i+=1
 while b%p==0:b//=p;i-=1
 return i
def mod(p,x):return (x.numerator*pow(x.denominator,-1,p))%p
def sec(L):
 X=(d*L**2-2*d*L-c)/(c+d*L**2); Z=1+L*(X-1)
 assert c*X*X+d*Z*Z==1;return X,Z
assert mod(41,d)==12 and pow(12,20,41)==40 and factorint(9145)=={5:1,31:1,59:1}
assert 9145%8==1 and 9145%3==1 and pow(9145,8,17)==1
for j,k in product(range(-5,6),range(5)):
 l=16+Q(M*j,7**k);X,Z=sec(l);b=b0*X*X
 test(b,E0*X*X,s0*X**2*Z,y0*X**3,z0*X**9*Z**3)
 assert [ord(p,b) for p in (2,3,17)]==[4,2,2] and all(ord(p,X)>=0 for p in (5,31,59)); assert isqrt(b.denominator)**2==b.denominator
 assert (1-b/17)==d*Z*Z and b/(w*X)**2==9145
print('seed',b0,'local residues of C',9145%8,9145%3,9145%17,'lambda=16',b0*sec(Q(16))[0]**2,'secant tests',55)
