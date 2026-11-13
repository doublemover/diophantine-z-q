from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json
import sympy as s

def root(v):
 if v<0:return None
 a,b=isqrt(v.numerator),isqrt(v.denominator)
 return F(a,b) if a*a==v.numerator and b*b==v.denominator else None

def add(n,P,Q):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 if x==z and y==-w:return None
 m=(3*x*x+4*n*x-3*n*n)/(2*y) if x==z else (y-w)/(x-z)
 u=m*m-2*n-x-z;v=m*(x-u)-y
 assert v*v==u*(u-n)*(u+3*n)
 return u,v

def coord(n,r,P):
 if P is None:return F(1)
 x,y=P
 return 3*r*r+4*n*r-3*n*n if x==r else x-r

allpts={n:{None,(F(0),F(0)),(F(n),F(0)),(F(-3*n),F(0))} for n in list(range(-30,0))+list(range(1,31))}
for n in allpts:
 for den in range(1,5):
  for num in range(-120,201):
   x=F(num,den*den);y=root(x*(x-n)*(x+3*n))
   if y is not None:allpts[n]|={(x,y),(x,-y)}
for n,pts in allpts.items():
 initial=sorted((P for P in pts if P is not None),key=lambda P:(P[0],P[1]))[:14]
 for P in initial:
  pts.add(add(n,P,P))
  for Q in initial[:6]:pts.add(add(n,P,Q))
products=identity_cases=inverse_cases=tangent_cases=exceptional_intersections=halves=exceptional_halves=0
for n,pts in allpts.items():
 for P in pts:
  for Q in pts:
   R=add(n,P,Q)
   if P is None or Q is None:identity_cases+=1
   elif R is None:inverse_cases+=1
   elif P[0]==Q[0]:tangent_cases+=1
   for r in [F(n),F(-3*n)]:
    a,b,c=coord(n,r,P),coord(n,r,Q),coord(n,r,R)
    assert a and b and c
    z=root(a*b*c)
    assert z is not None and z
    assert a*b==c*(z/c)**2
    products+=1
    if any(T is not None and T[0]==r for T in [P,Q,R]):exceptional_intersections+=1
  if P is None:continue
  x,y=P;rs=root(coord(n,F(-3*n),P));rt=root(coord(n,F(n),P))
  if rs is None or rt is None:continue
  if x==0:a,b,c=F(0),rt,rs;exceptional_halves+=1
  elif x==n:a,b,c=rs/2,F(0),rs;exceptional_halves+=1
  elif x==-3*n:a,b,c=rs*rt/(4*n),rt,F(0);exceptional_halves+=1
  else:c,b=rs,rt;a=-y/(b*c)
  assert a*a==x and b*b==x-n and c*c==x+3*n and a*b*c==-y
  H=(x+a*b+a*c+b*c,-(a+b)*(a+c)*(b+c))
  assert H[1] and add(n,H,H)==P;halves+=1
r,x,y,m,n=s.symbols('r x y m n');T=s.symbols('T');f=T*(T-n)*(T+3*n);L=m*(T-x)+y
assert s.expand(s.diff(f-L**2,T).subs(T,r)-(3*r*r+4*n*r-3*n*n-2*m*(m*(r-x)+y)))==0
result={'status':'PASS','twists':len(allpts),'actual_group_points':sum(map(len,allpts.values())),'actual_squareclass_products':products,'infinity_pair_cases':identity_cases,'inverse_pair_cases':inverse_cases,'tangent_pair_cases':tangent_cases,'two_torsion_intersections':exceptional_intersections,'actual_kernel_halves':halves,'exceptional_kernel_halves':exceptional_halves,'symbolic_derivative_checks':1,'scope':'Actual original group operations and complete Kummer coordinate branches; no prescribed beta-class rational point existence inferred.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
