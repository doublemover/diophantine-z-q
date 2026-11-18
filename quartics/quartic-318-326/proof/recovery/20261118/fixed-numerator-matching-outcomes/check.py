"""Two explicit globally successful slopes with exact opposite-sign and nontorsion controls."""
from fractions import Fraction as F
from math import isqrt,gcd
import json
bta=17
def root(x):
    x=F(x);a,b=isqrt(x.numerator),isqrt(x.denominator)
    assert F(a,b)**2==x;return F(a,b)
class K:
 def __init__(self,a=0,b=0):
    if isinstance(a,K):self.a,self.b=a.a,a.b
    else:self.a,self.b=F(a),F(b)
 def __add__(self,o):
    o=K(o);return K(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return K(-self.a,-self.b)
 def __sub__(self,o):return self+-K(o)
 def __rsub__(self,o):return K(o)+-self
 def __mul__(self,o):
    o=K(o);return K(self.a*o.a+bta*self.b*o.b,self.a*o.b+self.b*o.a)
 __rmul__=__mul__
 def inv(self):
    n=self.a**2-bta*self.b**2;return K(self.a/n,-self.b/n)
 def __truediv__(self,o):return self*K(o).inv()
 def __rtruediv__(self,o):return K(o)*self.inv()
 def __pow__(self,n):return K(1) if not n else self*self**(n-1)
def curve(n,x):return x*(x-n)*(x+3*n)
def run(k,t,th,r,ps,fs):
 b=bta;t=F(t);m=b*k*k;D=1-b*r*r;pole=17*b*r*r;B=17*pole;u=17*r
 assert D>0 and D<1 and root(D/th) and b==17 and pole==(17*r)**2
 assert r.denominator%2 and r.denominator%3 and r.denominator%17 and r.numerator%8==4 and r.numerator%3==0 and r.numerator%9 and r.numerator%17
 assert all(all(p%a for a in range(2,isqrt(p)+1)) for p in fs) and len(set(fs))==len(fs)
 from math import prod
 assert prod(fs)==th
 rad=(1-m)*(1-9*b*t*t)*((1+b*k*t)**2-9*b*(t+k)**2);y=root(th*rad)
 vv=(t+k)/(1+b*k*t)
 def slope(s):return 4*s/(1+3*b*s*s),2*(1-3*b*s*s)/(1+3*b*s*s)
 a,c=slope(t);a2,c2=slope(vv);e=1-b*a*a;e2=1-b*a2*a2;E=B*e;V=B*B*D
 S=root(V*e/e2);y1=b*b*u**3*a*c;y2=b*b*(u*S)**3*a2*c2
 assert E*S*y1*y2 and y1*y1==curve(E,B) and y2*y2==curve(E*V,B*S*S)
 bit=pow(r.denominator,(b-1)//2,b);bit=1 if bit==1 else -1
 assert bit==(1 if k==12 else -1)
 C=th*(1-m);r1=b*C*(25*m-9);r2=16*b*C*m;d=K(0,1);z=1/(3*d)
 undo=lambda z:(z-k)/(1-b*k*z)
 roots=[z,-z,undo(z),undo(-z)];g=-9*C*b*b*(m-9)
 A=g*(z-roots[1])*(z-roots[2])*(z-roots[3]);w=1/(t-z);u2=-1/(z-roots[1])
 X=A*(w-u2)/4;Y=A*y*w*w/8
 assert (Y**2-X*(X-r1)*(X-r2)).a==(Y**2-X*(X-r1)*(X-r2)).b==0
 lam=(3*X*X-2*(r1+r2)*X+r1*r2)/(2*Y)
 qx=lam**2+r1+r2-2*X;qy=lam*(X-qx)-Y
 assert qx.b==qy.b==0 and qy.a and qy.a**2==qx.a*(qx.a-r1)*(qx.a-r2)
 orders=[]
 for p in ps:
    assert r1*r2*(r1-r2)%p
    order=1+sum(1 if (d:=x*(x-r1)*(x-r2)%p)==0 else 2 if pow(d,(p-1)//2,p)==1 else 0 for x in range(p))
    orders.append(order)
 assert gcd(*orders)==4 and ps[0]%2 and ps[1]%2
 return dict(beta=b,k=k,t=str(t),theta=th,theta_factorization=fs,r=str(r),pole=str(pole),local_bit=bit,H_ordinate=str(y),point_pair={n:str(v) for n,v in zip(['E','S','y1','y2'],[E,S,y1,y2])},infinite_order_J_point=[str(qx.a),str(qy.a)],reduction_orders=dict(zip(ps,orders)))
if __name__=='__main__':
 print(json.dumps([run(4,1,66937,F(732,4519),[5,7],[13,19,271]),run(12,-4,654433,F(-2532,10471),[5,31],[13,50341])],indent=2))
