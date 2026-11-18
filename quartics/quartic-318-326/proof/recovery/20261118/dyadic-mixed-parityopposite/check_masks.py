from fractions import Fraction as F
from itertools import product
from sympy import symbols,expand
def mod(x):x=F(x);return x.numerator*pow(x.denominator,-1,4)%4
counts={1:0,-1:0}
for es,m,d,a,a3 in product(((0,32,76832,-343),(0,32,F(1120,3),375)),range(3),(-1,1),(-1,1),(-1,1)):
 j,k=[i for i in range(3) if i!=m];f=a3*(es[j]-es[3]);sg=1 if mod(F(f,a*d))==1 else -1
 assert mod(F(sg*f,a*d))==1 and len({d,-d,sg*d})==2
 counts[sg]+=1
assert counts=={1:24,-1:24}
s,R,J,X,Lx,Lz,bx,bz=symbols('s R J X Lx Lz bx bz')
eq=(X+s*J)**2+s*R*Lz*(X+s*J)-bz-(X**2+s*R*Lx*X-bx)
assert expand(eq-(s*s*J*J+(s*s*R*Lz+2*s*X)*J-(bz-bx)-s*R*(Lx-Lz)*X))==0
print('48 opposite types, 24 each delta comparison sign, genuine side subtraction identity checked')
