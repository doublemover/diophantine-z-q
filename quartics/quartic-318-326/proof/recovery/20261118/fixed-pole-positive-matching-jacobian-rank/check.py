"""Standard-library exact fixed-input controls; beta never confused with its five-prime part."""
from fractions import Fraction as F
from math import prod
import json
def val(x,p):
 x=F(x);n,d=x.numerator,x.denominator;v=0
 assert n
 while n%p==0:n//=p;v+=1
 while d%p==0:d//=p;v-=1
 return v
def run(beta,theta,r,z,s,t):
 assert 1-beta*r*r==theta*z*z and s*s+t*t==beta
 u=F(s,beta);v=F(t,beta);k=(r+u)/(1+beta*r*u);q=theta*z*v/(1+beta*r*u)
 m=beta*k*k;C=theta*(1-m);a=25*m-9;d=16*m;X=25*m;Y=45*m
 assert C==beta*q*q and X*(X-a)*(X-d)==Y*Y and Y
 assert X==beta*(5*k)**2 and X-a==9 and X-d==beta*(3*k)**2
 assert val(m,17)<0 and val(m,17)%2 and val(25-9/m,17)==val(9-9/m,17)==0
 a0=beta*C*(25*m-9);d0=16*beta*C*m;L=beta*q
 assert a0==L*L*a and d0==L*L*d and (L**3*Y)**2==(L**2*X)*(L**2*X-a0)*(L**2*X-d0)
 return dict(beta=beta,theta=theta,scale_r=str(r),slope=str(k),v17_m=val(m,17),q=str(q),normalized_X=str(X),normalized_Y=str(Y),ja=str(a/d))
if __name__=='__main__':
 out=[]
 for theta,l,e in [(409,1073,53),(457,439715,20569)]:
  for s,t in [(1,4),(4,1),(-1,4),(-4,1)]:out.append(run(17,theta,F(12,l),F(e,l),s,t))
 g=17*prod([409,2857,3673,6121,6529]);s,t=1466266519,875192144
 out.append(run(g,943689409057,F(12,20491203655),F(1,20491203655),s,t))
 cross=F(1,4);j=256*(1-cross+cross**2)**3/(cross**2*(1-cross)**2)
 lam=F(3*100**2-2*155*100+91*64,360);x2=lam**2+155-200
 assert x2==F(3364,25) and j==F(35152,9)
 print(json.dumps(dict(specialized_double_X=str(x2),geometric_double_cover_j=str(j),controls=out),indent=2))
