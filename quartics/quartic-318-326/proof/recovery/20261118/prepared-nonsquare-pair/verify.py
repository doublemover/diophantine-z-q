"""Exact replay, stdlib only. This is not a proof of density or a Lean run."""
from fractions import Fraction as F
from math import gcd, isqrt
import json
b0=F(1193493611520,227988105361)
C,K=b0/17,1-b0/17
N,M=155465,32*3*17*5*31*59
a,w,Y=F(1297,532),17*F(48,691)*F(14,691),F(149622419334526725,150568768)
u=2-51*F(48,691)**2
B0=17*b0
seed=(B0/a**2,B0/a,w**3*Y/a**3,B0**4*b0*u/a**3)

def pair(b,P):
    B=17*b; E,s,y1,y2=P; V=B**2*(1-b/17)
    return all((s,y1,y2,E,V)) and y1**2==B*(B-E)*(B+3*E) and y2**2==(B*s*s)*(B*s*s-E*V)*(B*s*s+3*E*V)

def cert(b,P):
    B=17*b; E,S,y1,y2=P
    e,s,p,q=E/b,S/b,y1/B,17*y2/(B**3*S)
    return 17*p*p==b*(17-e)*(17+3*e) and 17*q*q==b*(s*s-e*(17-b))*(s*s+3*e*(17-b))

def v(x,p):
    assert x
    n,d=x.numerator,x.denominator
    def val(n):
        k=0
        while n%p==0:k+=1;n//=p
        return k
    return val(n)-val(d)

def square(x):
    return x>=0 and isqrt(x.numerator)**2==x.numerator and isqrt(x.denominator)**2==x.denominator

def run(l):
    X=(K*l*l-2*K*l-C)/(C+K*l*l);Z=1+l*(X-1)
    assert C*X**2+K*Z**2==1
    E,s,y1,y2=seed
    b=b0*X**2
    P=E*X**2,s*X**2*Z,y1*X**3,y2*X**9*Z**3
    assert 0<b<17 and pair(b,P) and cert(b,P)
    assert [v(b,p) for p in [2,3,17]]==[4,2,2]
    assert isqrt(b.denominator)**2==b.denominator
    assert square(b/F(9145)) and square((1-b/17)/K) and not square(b) and not square(1-b/17)
    assert all(v(X,p)>=0 for p in (5,31,59))
    assert not square(4-3*b/17)
    return b,X,Z,P

def main():
    assert 9145==5*31*59 and all(all(p%d for d in range(2,isqrt(p)+1)) for p in (5,31,41,59))
    assert B0==N*w**2 and b0==9145*w**2 and (N*a*a)*(N*a*a-N)*(N*a*a+3*N)==Y**2
    assert 4-3*b0/17==u*u and K.numerator*pow(K.denominator,-1,41)%41==12 and pow(12,20,41)==40
    assert pair(b0,seed) and cert(b0,seed)
    tested=0
    for k in range(5):
        for j in range(-35,36):
            run(16+F(M*j,7**k)); tested+=1
    b,X,Z,P=run(F(16))
    assert b==F(22658301122605409802222416195208720,5695590725813967968465563114286281)
    assert not pair(b,(P[0],P[1],P[2],P[3]+1))
    assert not pair(b,(P[0]+1,P[1],P[2],P[3]))
    print(json.dumps(dict(status="EXACT_FINITE_REPLAY_PASS",cases=tested,seed=str(b0),
      slope16=dict(X=str(X),Z=str(Z),b=str(b),pointPair=list(map(str,P))),negative_controls=2),indent=2))
if __name__=='__main__':main()
