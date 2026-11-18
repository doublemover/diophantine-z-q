from fractions import Fraction as F
from itertools import product
from sympy import symbols,expand
def mod(x,m):
 x=F(x);return x.numerator*pow(x.denominator,-1,m)%m
u,b,w,d,a,a3,D,c=symbols('u b w d a a3 D c')
f=c+a3*d*u*u
expr=(2*b+u*w)**2-2*a*(1+u)**2*(d*u**2+D)
expr=expand(expr).subs(w**2,2*f)
rhs=b*b+u*w*b-a*D*(1+u)**2/2-u*u*((a*d-c)/2+a*d*u+d*(a-a3)*u*u/2)
assert expand(expr-4*rhs)==0
groups=[0,0];types=set()
for alt,es in enumerate(((0,32,76832,-343),(0,32,F(1120,3),375))):
 for m,d,a,a3 in product(range(3),(-1,1),(-1,1),(-1,1)):
  j,k=[i for i in range(3) if i!=m]; f=a3*(es[j]-es[3]); A=F(a*d-f,2)
  if mod(A,2)!=1:continue
  t=[d]*3;t[m]=2*a;t.append(2*a3)
  if alt:
   old=[0,32,76832];M=375*343
   # q'_3=-1/(M q_3), q'_i=q_i/q_3*(343+b_i)/M; map signs by modulo 4.
   q3=-a3 if M%4==1 else a3
   def rep(x):return 1 if mod(x,4)==1 else -1
   t=[(1 if i==m else 2)*rep(F((a if i==m else d)*q3*M,343+old[i])) for i in range(3)]+[2*q3]
  assert tuple(t) not in types;types.add(tuple(t))
  assert mod(F(es[j]-es[m],32),2)==1
  groups[j==1]+=1
assert len(types)==24 and groups==[16,8]
print('24 distinct original mixed-parity ordered types after inverse exchange, eight pair12, exact half-product identity')
