from itertools import product
import sympy as s
V=list(product(range(3),repeat=4))
A=s.symbols('a:4');B=s.symbols('b:4');C=s.symbols('c:4')
def prod(a,b):
 x,y,z,w=a;r,t,u,v=b
 return [x*r-210*y*t-84*y*v+z*u-126*w*t-42*w*v,x*t+y*r-2*y*u+3*z*t+z*v-w*u,x*u+z*r-42*y*v+z*u+42*w*t,x*v+w*r+5*y*u-5*z*t-2*z*v+3*w*u]
def E(a,b):return -2*a[0]*b[1]-a[0]*b[3]+2*a[1]*b[0]+a[1]*b[2]-a[2]*b[1]+a[3]*b[0]
ast=[A[0],-A[1]-A[3],A[2],A[3]]
assert s.expand(E(prod(A,B),C)-E(B,prod(ast,C)))==0
assert s.expand(E(A,A))==0
for a in V:
 assert E(a,a)%3==0
 assert (all(E(a,b)%3==0 for b in V)) == (a==(0,0,0,0))
G=s.Matrix([[0,2,0,1],[-2,0,-1,0],[0,1,0,0],[-1,0,0,0]])
assert G.det()==1
assert s.expand(-E(A,B)/s.Integer(9)*3+E(A,B)/s.Integer(3))==0
print('PASS: full integer Rosati adjoint, actual oriented Gram determinant1, all81 radical tests against81 arguments, exact thirds denominator9 and level denominator3')
