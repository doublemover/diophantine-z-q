#!/usr/bin/env python3
"""Independent exact checks; this is not a Lean/kernel or moduli-map proof."""
from pathlib import Path
import sympy as s
P=Path(__file__).resolve().parents[1]
A=[(-6,4,12,-5),(0,1,0,-1),(-14,5,28,-5),(-21,9,42,-10),(0,1,0,0)]
D=[30,42,70,105,210]
M=[[[1,-126,7,-84],[0,83,-4,56],[0,252,-13,168],[0,-105,5,-71]],[[1,0,1,0],[0,4,0,3],[0,0,-1,0],[0,-5,0,-4]],[[1,-210,15,-126],[0,74,-5,45],[0,420,-29,252],[0,-75,5,-46]],[[1,-336,22,-210],[0,143,-9,90],[0,672,-43,420],[0,-160,10,-101]],[[1,0,1,0],[0,1,0,1],[0,0,-1,0],[0,0,0,-1]]]
def vec(a):return '!['+','.join(map(str,a))+']'
def lin(row):return '+'.join(f'({x})*a {j}' for j,x in enumerate(row) if x) or '0'
assert vec([vec(a) for a in A]) in (P/'PELInertiaNormalizerData318.lean').read_text()
assert vec([vec([lin(r) for r in m]) for m in M]) in (P/'PELInertiaOrderInvolutions318.lean').read_text()
def mul(a,b):
 x,y,z,w=a;r,t,u,v=b
 return s.Matrix([x*r-210*y*t-84*y*v+z*u-126*w*t-42*w*v,x*t+y*r-2*y*u+3*z*t+z*v-w*u,x*u+z*r-42*y*v+z*u+42*w*t,x*v+w*r+5*y*u-5*z*t-2*z*v+3*w*u])
def bar(a):x,y,z,w=a;return s.Matrix([x+z,-y,-z,-w])
def norm(a):x,y,z,w=a;return x*x+x*z+210*y*y+210*y*w-z*z+42*w*w
def eq(a,b):assert all(s.expand(v)==0 for v in a-b),(a,b)
x=s.Matrix(s.symbols('x:4'));y=s.Matrix(s.symbols('y:4'))
alpha=s.sqrt(210);beta=s.sqrt(5)
for i,(a,d,m) in enumerate(zip(A,D,M)):
 a=s.Matrix(a);m=s.Matrix(m)
 assert norm(a)==d and 2*a[0]+a[2]==0
 eq(mul(a,a),s.Matrix([-d,0,0,0]));eq(m*m,s.eye(4))
 eq(m*x,mul(mul(a,x),bar(a))/d)
 eq(m*mul(x,y),mul(m*x,m*y))
 r=a[0]+a[2]/2;ii=a[1]+a[3]/2;j=a[2]/2;k=a[3]/10
 assert ii!=0
 rep=s.Matrix([[r+beta*j,-alpha*ii+alpha*beta*k],[alpha*ii+alpha*beta*k,r-beta*j]])
 assert s.simplify(rep.det()-d)==0 and rep.trace()==0
 assert rep[1,0]>0
 z=s.simplify((rep[0,0]+s.I*s.sqrt(d))/rep[1,0])
 assert s.im(z)>0
 assert s.simplify(rep[1,0]*z+rep[1,1]-s.I*s.sqrt(d))==0
 assert s.simplify(rep[0,0]*z+rep[0,1]-z*(rep[1,0]*z+rep[1,1]))==0
 # Literal quadratic embedding is multiplicative for arbitrary coefficients.
 u,v,w,t=s.symbols('u v w t');one=s.Matrix([1,0,0,0])
 eq(mul(u*one+v*a,w*one+t*a),(u*w-d*v*t)*one+(u*t+v*w)*a)
labels=[[1,1,1,0],[1,1,0,1],[1,0,1,1],[0,1,1,1],[1,1,1,1]]
assert [s.prod(p for p,e in zip([2,3,5,7],l) if e) for l in labels]==D
print('PASS: five literal inertia labels, original norms/traces/squares, whole conjugation/involutions, imaginary quadratic maps and exact positive fixed points. No contact branch or moduli-map identification asserted.')
