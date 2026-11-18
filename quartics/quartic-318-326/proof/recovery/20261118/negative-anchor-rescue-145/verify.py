from fractions import Fraction as F
from math import prod,isqrt,gcd
from itertools import product
import json
from local_images import img,pair
def sqrt(x):
 r=F(isqrt(x.numerator),isqrt(x.denominator));assert r*r==x;return r
def v(p,x):
 z=F(x);k=0;a=z.numerator;b=z.denominator
 while a%p==0:a//=p;k+=1
 while b%p==0:b//=p;k-=1
 return k
def chi(x,p):r=pow(x%p,(p-1)//2,p);assert r in (1,p-1);return 1 if r==1 else -1
def h2(x,y):
 va=v(2,x);vb=v(2,y);a=x//(2**va);b=y//(2**vb)
 return (-1)**(((a-1)//2*((b-1)//2)+va*((b*b-1)//8)+vb*((a*a-1)//8))%2)
def cubic(n,x):return x*(x-n)*(x+3*n)
def check(b,E,S,y1,y2):
 B=17*b;V=B**2*(1-b/17)
 assert B*V*E*S*y2 and cubic(E,B)==y1*y1 and cubic(E*V,B*S*S)==y2*y2
def main():
 m=145;beta=2465;theta=2449;N=beta*theta;A,Z,D=12,47,2401
 assert m==5*29 and beta==17*m and theta==31*79 and N==6036785
 qs=[2,3,5,17,29,31,79];assert all(all(p%q for q in range(2,isqrt(p)+1)) for p in qs)
 assert beta*A*A+theta*Z*Z==D*D and gcd(D,gcd(A,Z))==1
 b=m*F(17*A,D)**2;B=17*b;Comp=1-b/17;V=B*B*Comp
 assert b==F(6034320,5764801) and 0<b<17 and Comp==theta*F(Z,D)**2
 assert [v(p,b) for p in (2,3,17)]==[4,2,2] and m%8==m%3==1 and chi(m,17)==1
 assert isqrt(b.denominator)**2==b.denominator
 # positive anchor's exact local first-coordinate fiber
 I={p:img([0,N,-3*N],p) for p in [0]+qs}
 G=[prod(x**c for x,c in zip([-1]+qs,z)) for z in product((0,1),repeat=8)]
 locals_ok=lambda x,y:all(pair(x,y,p) in Q for p,Q in I.items())
 fiber=[y for y in G if locals_ok(theta,y)];assert fiber==[1]
 a,d=-17,-290;assert locals_ok(a,d);ell=2*D*5
 signs={'2':h2(ell,a)*h2(-ell,a*d),'3':(-1)**(v(3,a)%2),'infinity':1}
 for p in [5,17,29,31,79]:
  z=v(p,a)%2;zz=v(p,d)%2;signs[str(p)]=chi(-1,p)**z*chi(-2*D,p)**zz if beta%p==0 else chi(-2,p)**z*chi(-3*D,p)**zz
 assert {p for p,k in signs.items() if k==-1}=={'2','5','29'}
 # negative anchor, no rank, group law or search needed
 xx=F(668907746699090752665,40276074721);yy=F(17281222670980383356489001364800,8082965159682769)
 root=F(520924341,200689);assert beta*root**2==xx and yy**2==cubic(-3*N,xx)
 u=F(17*A,D);z0=B*F(Z,D);scale=u*z0/3
 E=-B/3;S=z0*root/3;y2=yy*scale**3
 assert E*V==-3*N*scale**2 and B*S*S==xx*scale*scale
 check(b,E,S,0,y2)
 # another solution at SAME b, both ordinates nonzero
 def one(z):return (z*z-3*beta)/(2*z),(z*z+3*beta)/(2*z)
 s,J=one(F(12));t,K=one(F(175));h=(s-t)/(s*t-beta);w=17*h
 b0=m*w*w;B0=17*b0;d0=1-b0/17;xs=u/w;zs=sqrt(Comp/d0)
 es=(s*s-beta)/J**2;E0=B0*es;S0=B0*K*(s*s-beta)/(J*(s*t-beta))
 yy1=w**3*beta*(4*beta*s/J**2);yy2=(w*S0)**3*beta*(4*beta*t/K**2)
 check(b0,E0,S0,yy1,yy2);check(b,E0*xs**2,S0*xs**2*zs,yy1*xs**3,yy2*xs**9*zs**3)
 assert yy1 and h==F(489,29881) and Comp==d0*zs**2
 return dict(b=str(b),m=m,beta=beta,theta=theta,depths=[4,2,2],positive_fiber_second=fiber,positive_CT_witness=[a,d],local_signs=signs,negative_anchor_point=[str(xx),str(yy)],two_seed_parameters=[12,175],transport=[str(xs),str(zs)],both_exact_solutions_checked=True)
if __name__=='__main__':print(json.dumps(main(),indent=2))
