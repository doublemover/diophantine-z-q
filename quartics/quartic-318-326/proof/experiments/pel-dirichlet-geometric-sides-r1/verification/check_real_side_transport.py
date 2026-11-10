"""Exact rational identities only; not a polygon-cover or genus proof."""
import sympy as S
x,y,a,b,c,d,alpha,beta=S.symbols('x y a b c d alpha beta',nonzero=True)
N=x*x+y*y+1;A=alpha*beta*2*x/N;B=beta*(x*x+y*y-1)/N
U=(a*x+b)**2+(a*y)**2;L=(c*x+d)**2+(c*y)**2;C=(a*x+b)*(c*x+d)+a*c*y*y
rows=[(a*d+b*c)*A+alpha*(a*c-b*d)*B+alpha*beta*(a*c+b*d),
 (a*b-c*d)/alpha*A+(a*a-b*b-c*c+d*d)/2*B+beta*(a*a+b*b-c*c-d*d)/2,
 (a*b+c*d)/(alpha*beta)*A+(a*a+c*c-b*b-d*d)/(2*beta)*B+(a*a+b*b+c*c+d*d)/2]
for lhs,rhs in zip(rows,[alpha*beta*2*C/N,beta*(U-L)/N,(U+L)/N]):assert S.factor(lhs-rhs)==0
r0,r1,r2,p0,p1,q0,q1,s=S.symbols('r0 r1 r2 p0 p1 q0 q1 s')
f=lambda u,v:r0*u+r1*v+r2
assert S.expand(f((1-s)*p0+s*q0,(1-s)*p1+s*q1)-((1-s)*f(p0,p1)+s*f(q0,q1)))==0
print('PASS: all3 original Klein rows and real affine whole-side identity; no Lean or covering claim.')
