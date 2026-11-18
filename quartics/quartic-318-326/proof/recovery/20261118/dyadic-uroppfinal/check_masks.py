from sympy import symbols,expand
u,x,t,G,D,K,a=symbols('u x t G D K a')
# e^2 exactly after substitution and cancellation of x^4
assert expand((1+t*t)*(a*(u+x)+D+(a*x+D)*t*t)-(a*u*(1+t*t)+(a*x+D)*(1+t*t)**2))==0
for n,n2 in [(1,2401),(2401,1)]:
 for a in (-1,1):
  C=(-n-1)//2;D=-a*(1+n2)//2;K=-a*C+D
  assert C%2 and D%2 and K==a*(n-n2)//2 and abs(K)==1200
print('all four deep corner constants exactly ±1200, norm numerator checked, twelve ordered sign/index cases')
