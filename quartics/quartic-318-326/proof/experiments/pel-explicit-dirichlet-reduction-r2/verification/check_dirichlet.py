"""Supplementary exact arithmetic only. Not Lean or a fundamental-domain proof."""
from fractions import Fraction as Q
import itertools
import sympy as S
rows=[(672,Q(104,5),0),(222,Q(34,5),18),(8232,Q(1204,5),1176),
      (980,28,168),(4200,116,840),(1125,30,255),(222,Q(26,5),66),(5,0,3)]
base=[(-13,-2,0,4),(1,-1,-6,1),(-43,-8,0,14),(13,-1,-14,0),
      (-29,-6,0,10),(16,-1,-15,0),(5,-1,-6,1),(2,0,-1,0)]
def norm(a):
 a,b,c,d=a
 return a*a+a*c+210*b*b+210*b*d-c*c+42*d*d
def flip1(a):a,b,c,d=a;return a,-b,c,-d
def flip2(a):a,b,c,d=a;return -a-c,b+d,c,-d
def coords(a):a,b,c,d=map(Q,a);return a+c/2,b+d/2,c/2,d/10
for k,(e,f) in itertools.product(range(8),itertools.product([False,True],repeat=2)):
 a=base[k]
 if e:a=flip1(a)
 if f:a=flip2(a)
 assert norm(a)==1
 r,i,j,t=coords(a);C,U,V=rows[k]
 assert 2*r*r+420*i*i+10*j*j+2100*t*t-2==C
 assert 4*(r*t-i*j)==-U*(-1 if e else 1)
 assert 4*r*j+840*i*t==-V*(-1 if f else 1)
ends=[Q(0),Q(5,39),Q(75,109),Q(35,48),Q(35,36),Q(75,73),Q(135,109),Q(5,3)]
slopes=[(0,Q(420,13)),(Q(-45,17),Q(555,17)),(Q(-210,43),Q(1470,43)),
        (-6,35),(Q(-210,29),Q(1050,29)),(Q(-17,2),Q(75,2)),(Q(-165,13),Q(555,13))]
for k,(m,c) in enumerate(slopes):
 for b in ends[k:k+2]:
  a=m*b+c
  assert a>=0 and a*a/1050+b*b/5<=Q(9999,10000)
 # The quadratic on the strip is convex, so the endpoints bound its maximum.
 assert Q(m*m,1050)+Q(1,5)>0
x,y=S.symbols('x y',real=True);a,b,c,d=S.symbols('a b c d',real=True)
H=(x*x+y*y+1)/y;u=2*x/(x*x+y*y+1);v=(x*x+y*y-1)/(x*x+y*y+1)
assert S.factor((1-u*u-v*v)*H*H-4)==0
Hprime=((a*x+b)**2+(a*y)**2+(c*x+d)**2+(c*y)**2)/y
energy=a*a+b*b+c*c+d*d-2+2*(a*b+c*d)*u+(a*a+c*c-b*b-d*d)*v
assert S.factor(2*(Hprime-H)/H-energy)==0
r,i,j,k=S.symbols('r i j k',real=True)
M={a:r+S.sqrt(5)*j,b:-S.sqrt(210)*i+S.sqrt(1050)*k,
   c:S.sqrt(210)*i+S.sqrt(1050)*k,d:r-S.sqrt(5)*j}
assert S.simplify((a*a+b*b+c*c+d*d-2).subs(M)-(2*r*r+420*i*i+10*j*j+2100*k*k-2))==0
assert S.simplify((2*(a*b+c*d)).subs(M)-S.sqrt(1050)*4*(r*k-i*j))==0
assert S.simplify((a*a+c*c-b*b-d*d).subs(M)-S.sqrt(5)*(4*r*j+840*i*k))==0
print('PASS: 32 original unit rows, all7 strip endpoint/convexity certificates, exact original height and Klein identities. Not a Lean proof or fundamental-domain certification.')
