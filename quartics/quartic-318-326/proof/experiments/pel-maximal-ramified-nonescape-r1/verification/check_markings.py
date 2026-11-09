from itertools import product
import sympy as s
A=s.symbols('a:4');B=s.symbols('b:4');C=s.symbols('c:4')
def prod(a,b):
 x,y,z,w=a;r,t,u,v=b
 return [x*r-210*y*t-84*y*v+z*u-126*w*t-42*w*v,x*t+y*r-2*y*u+3*z*t+z*v-w*u,x*u+z*r-42*y*v+z*u+42*w*t,x*v+w*r+5*y*u-5*z*t-2*z*v+3*w*u]
def E(a,b):return -2*a[0]*b[1]-a[0]*b[3]+2*a[1]*b[0]+a[1]*b[2]-a[2]*b[1]+a[3]*b[0]
def N(c):return c[0]**2+c[0]*c[2]+210*c[1]**2+210*c[1]*c[3]-c[2]**2+42*c[3]**2
assert s.expand(E(prod(A,C),prod(B,C))-N(C)*E(A,B))==0
V=list(product(range(3),repeat=4));units=[a for a in V if N(a)%3]
assert len(units)==72
mod=lambda a:tuple(x%3 for x in a)
for u in units:
 images={mod(prod(a,u)) for a in V};assert len(images)==81
 for a in V:assert N(u)%3!=0
assert len([u for u in units if N(u)%3==1])==36
assert len([u for u in units if N(u)%3==2])==36
print('PASS original integer norm similitude,72 invertible right-regular permutations on81 classes, both nonzero multiplier classes present; Lean does not yet assert the separate36 norm-one count')
