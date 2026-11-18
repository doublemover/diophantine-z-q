"""Exact arithmetic controls for a coherent (global, Selmer) pair."""
from fractions import Fraction as F
from math import isqrt
import json

def vp(a,p):
    assert a
    n,d=a.numerator,a.denominator;v=0
    while n%p==0:v+=1;n//=p
    while d%p==0:v-=1;d//=p
    return v
def prime(p):return p>=2 and all(p%k for k in range(2,isqrt(p)+1))
def square(a):return a>=0 and isqrt(a.numerator)**2==a.numerator and isqrt(a.denominator)**2==a.denominator
def example(b,beta,theta,q):
    B=17*b;D=1-b/17;V=B*B*D
    assert square(B/beta) and square(D/theta)
    u=F(isqrt((B/beta).numerator),isqrt((B/beta).denominator));M=6*beta*theta
    assert prime(q) and M%q and pow(beta%q,(q-1)//2,q)==1
    t=next(k*M for k in range(1,3*q+1) if vp(F(1-beta*(k*M)**2),q)==1)
    s=F(2*t,1-3*beta*t*t);L=F(1+3*beta*t*t,1-3*beta*t*t)
    e=F((1-beta*t*t)*(1-9*beta*t*t),(1+3*beta*t*t)**2)
    assert 1+3*beta*s*s==L*L and e==(1-beta*s*s)/(L*L)
    E=B*e;n2=E*V;y=4*beta**2*u**3*s/(L*L)
    assert y and y*y==B*(B-E)*(B+3*E)
    assert B-E==(2*beta*u*s/L)**2 and B+3*E==beta*(2*u/L)**2
    assert vp(e,q)==1 and vp(n2,q)%2 and vp(B,q)%2==0
    for p in (2,3,17):
        assert vp(1-e,p)>=(3 if p==2 else 1)
    return {'b':str(b),'beta':beta,'theta':theta,'q':q,'t':str(t),'e':str(e),'first_nonzero':True}
if __name__=='__main__':
 print(json.dumps([example(F(204,1073)**2,17,409,13),example(F(6034320,5764801),2465,2449,11)],indent=2))
