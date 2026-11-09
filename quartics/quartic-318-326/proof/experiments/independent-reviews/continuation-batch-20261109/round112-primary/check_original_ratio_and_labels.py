from itertools import product
import sympy as s
D,u,v,k,m=s.symbols('D u v k m')
t=(k*v/u-m)/(k*k+D*u*u);B=k*k+m*t+D*u*u*t*t;a=-1/k;b=m/k**2
V=(v*b*(1-D*u*u*a*a)-2*D*u*a*(u*u+a*a))/(1+D*u*u*a*a)**2
num=s.together(V-u*B/k).as_numer_denom()[0]
g=s.groebner([v*v-1+D*u**4,m*m-k**4+D],v,m,u,k,D)
assert g.reduce(s.expand(num))[1]==0
Div=[n for n in range(1,211) if 210%n==0]
E=[(n,t) for n in Div for t in range(-28,29) if t*t<4*n and t*t%n==0 and t]
assert set(E)=={(1,-1),(1,1),(2,-2),(2,2),(3,-3),(3,3)}
assert [n for n in Div if n%3 in (0,1) and n%5 in (0,2,3) and n%7 in (0,1,2,4) and n%8!=7]==[30,42,70,105,210]
assert all((-5*x*x+2*y*y+2*y*z+2*z*z)%8!=7 for x,y,z in product(range(8),repeat=3))
print('PASS: independent original translated ordinate, all210-supported elliptic trace cases,512 dyadic residues; no orbit-count inference')
