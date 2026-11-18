from fractions import Fraction as F
import json
from math import isqrt
def sqrt(x):
 x=F(x); n=isqrt(x.numerator); d=isqrt(x.denominator); assert n*n==x.numerator and d*d==x.denominator; return F(n,d)
def add(P,Q,H):
 if P is None:return Q
 if Q is None:return P
 x,y=P; z,w=Q
 if x==z and y==-w:return None
 m=(w-y)/(z-x) if x!=z else (3*x*x+2*(4-H)*x-4*H)/(2*y)
 h=m*m-4+H-x-z
 return h,m*(x-h)-y
def inverse(P,R):
 x,y=P;D=1-R; H=3*D/R
 U=sqrt(x/D); V=sqrt(x+4); W=y/(D*U*V);assert D*W*W==x-H
 M=R*U/2;K=R*V/2;L=R*W;t=(K-L)/(2*(R+3));lam=L+6*t
 assert M*M==lam*lam+12*R*t*t and R==(lam+2*t)**2-16*D*t*t
 return map(str,(lam,M,t))
def main():
 tests=0
 for j in range(2,18):
  for i in range(1,j):
   R=F(i,j);D=1-R
   for lam,t in [(F(2),F(1)),(F(-7,9),F(17,4)),(F(23),F(0))]:
    M2=lam*lam+12*R*t*t;s2=((lam+2*t)**2-16*D*t*t)/R
    L=lam-6*t;K=lam+2*R*t
    assert L*L==4*M2-3*R*s2 and K*K==D*M2+R*R*s2
    assert (K-L)/(2*(R+3))==t
    tests+=1
 R=F(2448,8281);D=1-R;H=3*D/R
 lam=F(2);M=F(250,91);s=F(4);L=lam-6;K=lam+2*R
 U=2*M/(R*s);V=2*K/(R*s);W=L/(R*s)
 P=(D*U*U,D*U*V*W);x,y=P
 assert y*y==x*(x+4)*(x-H) and x+4==V*V and x-H==D*W*W
 P2=add(P,P,H);A=P
 for i in range(6):
  list(inverse(A,R))
  A=add(A,P2,H)
 return dict(diagonalization_checks=tests,standalone=dict(b=str(17*R),R=str(R),D=str(D),x=str(x),y=str(y),inverted_odd_multiples=[1,3,5,7,9,11]))
if __name__=="__main__":print(json.dumps(main(),indent=2))
