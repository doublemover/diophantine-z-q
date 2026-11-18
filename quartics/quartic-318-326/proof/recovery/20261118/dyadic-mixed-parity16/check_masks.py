from fractions import Fraction as F
from itertools import product
from sympy import symbols,expand
S,K=symbols('S K');assert expand((S+2*K)**2-(S*S+4*K*(1+S))-4*K*(K-1))==0
def mod(x):x=F(x);return x.numerator*pow(x.denominator,-1,4)%4
g={1:0,3:0}
for es,m,d,a,a3 in product(((0,32,76832,-343),(0,32,F(1120,3),375)),(1,2),(-1,1),(-1,1),(-1,1)):
 k=3-m;fo=-a3*es[3]
 if mod(F(a*d-fo,2))%2==0:continue
 H=F(-d*es[k],32);M=F(-a*es[m],32);K=M/(a*d*H);Gamma=-H/((2*K-1)*fo**3)
 assert mod(F(-fo,a*d))==1 and mod((K-1)/32)%2==1
 g[mod(Gamma)]+=1
assert g=={1:8,3:8}
print('checked 16 odd-A0 mixed parity cases, both exact norms and eight/eight split regimes')
