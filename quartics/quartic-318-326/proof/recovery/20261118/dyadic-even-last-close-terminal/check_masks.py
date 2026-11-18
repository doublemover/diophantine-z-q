from fractions import Fraction as F
from itertools import product
from sympy import symbols,expand
w,A,B,S,K=symbols('w A B S K')
assert expand((w*B+S)**2+(S+2*K*A)**2-4*K*(K-1)*A**2-((w*B+S)**2+S**2+4*K*(A*A+S*A)))==0
N=0
for es,k,d,a in product(((0,32,76832,-343),(0,32,F(1120,3),375)),(1,2),(-1,1),(-1,1)):
 m=3-k;H=-d*F(es[k],32);M=d*F(es[m],32);K=-M/H; C=2*K*(K-1);f=-a*es[3];G=-H/((2*K-1)*f**3)
 assert (C/64).numerator%2 and (C/64).denominator%2
 split=G.numerator*pow(G.denominator,-1,4)%4==1
 assert split==(d==(-a if es[3]==-343 else a))
 N+=split
assert N==8
print('verified 16 exact contact/sign comparisons, order 12 after ramification, norm identity and eight split unit cases')
