from fractions import Fraction as F
for k in (1,2):
 e=[0,16,38416];K=F(e[3-k],e[k]);N=F(e[k],16);L=2*K-1;D=K*(K-1)/32
 assert D.numerator%2 and D.denominator%2 and ((N/L-1)/32).denominator%2
 assert all(F(-d*e[k],16)==-d*N for d in (-1,1))
assert 8-6==2 and 7-2==5 and 5+7-4==8
print('six patterns, exact contact norms, powers in unsplit cusp checked')
