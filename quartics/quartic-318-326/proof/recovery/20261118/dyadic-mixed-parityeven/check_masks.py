from fractions import Fraction as F
from itertools import product
from collections import Counter
from sympy import symbols,expand
def mod(x):x=F(x);return x.numerator*pow(x.denominator,-1,4)%4
counts=Counter()
for es,m,d,a,a3 in product(((0,32,76832,-343),(0,32,F(1120,3),375)),range(3),(-1,1),(-1,1),(-1,1)):
 j,k=[i for i in range(3) if i!=m];f=a3*(es[j]-es[3]);A=F(a*d-f,2)
 if mod(A)%2:continue
 H=F(d*(es[j]-es[k]),32 if j==0 else 1024);M=F(a*(es[j]-es[m]),32)
 assert mod(H)%2 and mod(M)%2
 if j==0:
  K=M/(a*d*H);r=-H/((2*K-1)*f**3);assert mod(F(f,a*d))==1 and mod((K-1)/32)%2
 else:r=M/f**4
 counts[j,mod(r)]+=1
assert sum(counts.values())==24 and {j:sum(n for (k,_),n in counts.items() if j==k) for j in (0,1)}=={0:16,1:8}
w,P,Z,E,A,d,C,M=symbols('w P Z E A d C M')
eq=lambda x,y:expand(x-y)==0
assert eq((w*w*Z)**2+w*(w*P)*(w*w*Z)-(w*P)**2*(w*w*A+d*w*w*P+C*w**4*P**2)-M*w**6,w**4*(Z**2+P*Z-P**2*(A+d*P+C*w*w*P**2)-M*w*w))
print('24 complementary mixed types; split-contact regimes',sorted(counts.items()),'normalized scale verified')
