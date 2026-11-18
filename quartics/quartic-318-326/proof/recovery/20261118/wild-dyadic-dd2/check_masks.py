from sympy import Rational,expand,symbols
from itertools import product
Q,v,z,m,c,a,d=symbols('Q v z m c a d')
assert expand((v*Q)*a*d*v**2+(v*Q)**2*a*d*v+(v*Q)**3*c-(v*Q)**2*m*v*z-v**2*(v*Q*(a*d+a*d*Q+c*Q**2-m*Q*z)))==0
for d,a in product((1,-1),repeat=2):
 m=(1-d)//2
 assert (a*(343+d)-2*m*m)%4==0
 c=(4801-Rational(d,(343*a)**3))/2
 assert c.q%2
 assert c.p%2==(d*a==1)
 if d*a==-1: assert (c/2).q%2 and (c/2).p%2==0
print('four sign pairs; shifted node charts; exact exceptional parity cases OK')
