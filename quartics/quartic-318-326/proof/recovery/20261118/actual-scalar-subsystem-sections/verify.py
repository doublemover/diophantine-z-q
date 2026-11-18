"""Exact rational controls for the paper; no search, CAS, or network required."""
from fractions import Fraction as F
from math import prod,isqrt
from pathlib import Path
import json

def vp(k,p):
    z=0
    while k%p==0:
        k//=p;z+=1
    return z
def val(a,p):return vp(a.numerator,p)-vp(a.denominator,p)
def mod(a,p):return a.numerator*pow(a.denominator,-1,p)%p
def check():
    f=Path(__file__).with_name("SEED.json")
    d={k:F(v) for k,v in json.loads(f.read_text()).items()}
    r=4376874610839020;A=114444*r;m=11*r//4;bt=17*m
    ps=[5,11,163,661,733,1489,1861];support=[2,3,17]+ps
    assert all(all(p%k for k in range(2,isqrt(p)+1)) for p in support)
    assert m==prod(ps) and A==204**2*m
    assert [m%p for p in [8,3,17]]==[1,1,1]
    j=d['j'];w=d['W'];n=d['n'];q=d['q'];h=d['H'];c=d['C'];b=d['b']
    assert j==d['P']/d['Q0'] and all(mod(j,p)==1 for p in support)
    U=1+36*bt*j*j
    assert w==(1+A)*j/U==n*n+r*q*q and q and 1<n and 1<w<F(106,100)
    assert h==12*j/U and c==(1-36*bt*j*j)/U and c*c==1-b/17
    assert b==m*(17*h)**2==A*(w/(1+A))**2 and 0<b<17
    assert [val(b,p) for p in [2,3,17]]==[4,2,2]
    assert isqrt(b.denominator)**2==b.denominator and all(mod(w,p)==1 for p in support)
    B=17*b;V=B*B*(1-b/17);v=17*h
    e0=F(1-bt,1+3*bt);u0=F(4*bt,1+3*bt)
    assert u0**2==bt*(1-e0)*(1+3*e0)
    E=B*e0;S=B*c;y1=bt*v**3*u0;y2=y1*S**3
    assert E and S and y1 and y2 and V==S*S
    assert y1*y1==B*(B-E)*(B+3*E) and y2*y2==B*S*S*(B*S*S-E*V)*(B*S*S+3*E*V)
    es=E/b;ss=S/b;pp=y1/B;qq=17*y2/(B**3*S)
    assert 17*pp**2==b*(17-es)*(17+3*es)
    assert 17*qq**2==b*(ss**2-es*(17-b))*(ss**2+3*es*(17-b))
    K=(1+A)/w;G=36*bt*K;X=G*j;Y=G*U;C=36*bt*K*K
    assert Y*Y==X**3+C*X and Y and C>0 and val(C,17)%2
    guards={}
    for p in (7,19):
        k=mod(C,p)
        count=1+sum((y*y-x**3-k*x)%p==0 for x in range(p) for y in range(p))
        assert k and count==p+1
        guards[str(p)]=[k,count]
    # Every legal |c_n|<1, guarded w33 in [0,1], |w37| in [1/100,1].
    assert (1+F(1,r*r)+F(2,r))**2+F(10000,r**29)<2
    assert (1+A)**2>24**2*bt
    for rootnorm in (F(1,17),F(-141,8183)):
        H=rootnorm/(q*r**15);J=F(r,2)*(n-1-(H/r)**2)
        assert n==1+(H/r)**2+2*J/r and q==rootnorm/(H*r**15)
    return {"r":r,"A":A,"m":m,"beta":bt,"finite_support":sorted(support),
       "depths":[4,2,2],"positive_rank_fiber_mod_p":[guards[str(p)] for p in (7,19)],
       "scalar_rows":[263,281],"certificate_rows":[282,286],
       "exact_seed_real_guard_claim":False,"common_H_produced":False}
if __name__=='__main__':print(json.dumps(check(),indent=2))
