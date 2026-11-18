from sympy import symbols,expand
q,C,D,K=symbols('q C D K');P=q-1;t=1+2*P+2*P**2
assert expand(t*((1-D)/2+P)+(t-K)*P**2/2-(q**4-q**3+(-D-K/2+1/2)*q**2+(D+K)*q-(D+K)/2))==0
for a in (-1,1):
 for i,j in ((1,2401),(2401,1)):
  assert abs(a*i-a*j)==2400
print('quartic identity; exact constant order four after halving; twelve original signs and minority choices')
