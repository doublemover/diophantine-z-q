from sympy import symbols,expand
from itertools import product
pi,U,Z,a,b=symbols('pi U Z a b')
assert expand((pi*Z+U+1)**2-a*U**2-b-(pi**2*Z**2+2*pi*(U+1)*Z+(1-a)*U**2+2*U+1-b))==0
count=0
for d0,d1,d2,d3 in product((1,-1),repeat=4):
 if d0==d1==d2: continue
 count+=1
 for a,b in [(d3*d0,343*d3),(343*d3,d3*d0)]:
  assert (1-a)%2==0 and (1-b)%2==0
  assert expand(((1-a)//2*U**2+U+(1-b)//2).diff(U)).subs(U,1)%2==1
assert count==12
print('12 mixed odd sign representatives; both exact quartic shifts and unit residue derivatives verified')
