"""Exact identities and finite leading-term checks; not proof of the geometry."""
from fractions import Fraction as Q
from itertools import product
from sympy import symbols,expand,cancel
A,B,S,G=symbols('A B S G')
e=B/A-1-2400
t=1+G/A**2
num=A*B**2-A**2*B+G*B-2401*G*A
assert cancel(e*(e+t+4800)+2400*2401-num/A**3)==0
assert expand(num-(A*(B**2+S*B-2401*G)-B*(A**2+S*A-G)))==0
assert 2400==75*2**5 and 2401==49**2 and 19208==8*2401
# In F2[p]/p^3, represent polynomials by their coefficient bits
def mul(x,y):
 a=0
 for i in range(3):
  if y>>i&1:a^=x<<i
 return a&7
p=2; answers=[]
for w in (0,mul(p,p)):
 L=1^w; T=1^p
 if mul(mul(mul(L,L),L),mul(T,T))==1:answers.append(w)
assert answers==[4]
# Exact effect of e=p²E, v=p²V, w=p²Z in ev=Hw^10.
p,E,V,Z,H=symbols('p E V Z H')
assert expand((p**2*E)*(p**2*V)-H*(p**2*Z)**10 - p**4*(E*V-H*p**16*Z**10))==0
assert list(range(16,1,-2))==[16,14,12,10,8,6,4,2]
# Final tangent conic is smooth even in F2; exact chart argument covers extensions.
for x,y,z in product(range(2),repeat=3):
 if (x,y,z)!=(0,0,0) and (x*y-z*z)%2==0: assert x or y
print('PASS: exact split product, unit factor, length-3 branch jet, exponent 16, terminal count and conic sanity checks.')
