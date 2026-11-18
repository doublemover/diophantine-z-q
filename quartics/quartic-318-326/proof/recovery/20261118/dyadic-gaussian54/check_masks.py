from fractions import Fraction as F
from sympy import symbols,expand
c=[0,8,19208]
for k in (1,2):
 m=3-k;K=F(c[m],c[k]);N=F(c[k],8);L=2*K-1
 assert (K-1).numerator%32==0 and (K-1).numerator%64!=0
 assert ((N/L-1)/32).denominator%2
a,b,c=3,18,22
for _ in range(3):
 assert a>=1 and b>=2 and c>=6
 p,P,Z,M,B,N,U=symbols('p P Z M B N U'); S=p*P;V=p*p*Z
 old=V**2+p**a*M*S*V+p*B*S**3+p**b*N*S**2-U*p**(c-2)
 a,b,c=a-1,b-2,c-6
 assert expand(old-p**4*(Z**2+p**a*M*P*Z+(B*P+p**b*N)*P**2-U*p**c))==0
assert(a,b,c)==(0,12,4)
print('two contact ratios order five, quadratic cancellation, all three exact cusp-cycle exponents')
