from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path
import sympy as s
x,y,n,a,b,c=s.symbols('x y n a b c');X=x+a*b+a*c+b*c;Y=-(a+b)*(a+c)*(b+c);m=-(a+b+c)
rels=[a*a-x,b*b-x+n,c*c-x-3*n]
polys=[X-(a+b)*(a+c),X-n-(a+b)*(b+c),X+3*n-(a+c)*(b+c),Y*Y-X*(X-n)*(X+3*n),2*Y*m-(3*X*X+4*n*X-3*n*n),m*m-2*n-2*X-x]
for z in polys:assert s.reduced(s.expand(z),rels,a,b,c,x,n)[1]==0
assert s.expand(m*(X-x)-Y+a*b*c)==0
N=3*x*x+4*n*x-3*n*n;C=y*y-x*(x-n)*(x+3*n)
for off,num in [(0,x*x+3*n*n),(-n,(x-n)**2-4*n*n),(3*n,(x+3*n)**2-12*n*n)]:
 assert s.div(s.expand(N*N+4*y*y*(-2*n-2*x+off)-num*num),C,y)[1]==0
points=set();doubles=halves=translations=0
for nn in range(1,41):
 for den in range(1,7):
  for num in range(-150,251):
   xx=F(num,den*den);v=xx*(xx-nn)*(xx+3*nn)
   if v<=0:continue
   r,t=isqrt(v.numerator),isqrt(v.denominator)
   if r*r!=v.numerator or t*t!=v.denominator:continue
   for yy in [F(r,t),-F(r,t)]:points.add((nn,xx,yy))
for nn,xx,yy in points:
 mm=(3*xx*xx+4*nn*xx-3*nn*nn)/(2*yy);dx=mm*mm-2*nn-2*xx;dy=mm*(xx-dx)-yy
 assert dy*dy==dx*(dx-nn)*(dx+3*nn)
 aa=(xx*xx+3*nn*nn)/(2*yy);bb=((xx-nn)**2-4*nn*nn)/(2*yy);cc=((xx+3*nn)**2-12*nn*nn)/(2*yy)
 assert aa*aa==dx and bb*bb==dx-nn and cc*cc==dx+3*nn;doubles+=1
 if dx and dx-nn and dx+3*nn:
  aa=-dy/(bb*cc);assert aa*aa==dx
  hx=dx+aa*bb+aa*cc+bb*cc;hy=-(aa+bb)*(aa+cc)*(bb+cc);hm=-(aa+bb+cc)
  assert hy and hy*hy==hx*(hx-nn)*(hx+3*nn)
  assert hm==(3*hx*hx+4*nn*hx-3*nn*nn)/(2*hy)
  assert hm*hm-2*nn-2*hx==dx and hm*(hx-dx)-hy==dy;halves+=1
 tx=-3*nn*(xx-nn)/(xx+3*nn);ty=-12*nn*nn*yy/(xx+3*nn)**2;tm=yy/(xx+3*nn)
 assert tm*tm-2*nn-xx+3*nn==tx and tm*(xx-tx)-yy==ty
 assert ty*ty==tx*(tx-nn)*(tx+3*nn);translations+=1
result={'status':'PASS','symbolic_halving_identities':7,'symbolic_double_square_identities':3,'actual_rational_points':len(points),'actual_doubles':doubles,'actual_halves':halves,'actual_torsion_additions':translations,'scope':'Exact original elliptic group coordinate regressions; no global beta-class existence claim.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
