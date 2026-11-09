#!/usr/bin/env python3
"""Exact symbolic and finite sanity checks; not Lean or a proof of universality."""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json
import sympy as s

HERE=Path(__file__).resolve().parent
u,D=s.symbols('u D')
vdouble=(1-6*D*u**4+D**2*u**8)/(1+D*u**4)**2
assert s.cancel(vdouble-1+8*D*u**4/(1+D*u**4)**2)==0
ar,ai,br,bi=s.symbols('ar ai br bi')
i=s.sqrt(2)
assert s.expand((ar+ai*i)*(br+bi*i)-(ar*br+2*ai*bi+(ar*bi+ai*br)*i))==0
assert s.cancel((ar+ai*i)*(ar-ai*i)/(ar**2-2*ai**2)-1)==0
# Exact translation at the positive identity, including original v orientation.
a,b,d,x,y=s.symbols('a b d x y')
SU=(a*y+x*b)/(1+d*a*a*x*x)
SV=(b*y*(1-d*a*a*x*x)-2*d*a*x*(a*a+x*x))/(1+d*a*a*x*x)**2
assert SU.subs({x:0,y:1})==a and SV.subs({x:0,y:1})==b

@dataclass(frozen=True)
class K:
    re: Q
    im: Q=Q(0)
    def __post_init__(self):
        object.__setattr__(self,'re',Q(self.re)); object.__setattr__(self,'im',Q(self.im))
    def __add__(self,z):
        z=z if isinstance(z,K) else K(z); return K(self.re+z.re,self.im+z.im)
    __radd__=__add__
    def __neg__(self): return K(-self.re,-self.im)
    def __sub__(self,z): return self+-asK(z)
    def __rsub__(self,z): return asK(z)+-self
    def __mul__(self,z):
        z=asK(z); return K(self.re*z.re+2*self.im*z.im,self.re*z.im+self.im*z.re)
    __rmul__=__mul__
    def norm(self): return self.re**2-2*self.im**2
    def __truediv__(self,z):
        z=asK(z); assert z.norm()!=0
        return self*K(z.re/z.norm(),-z.im/z.norm())
    def __rtruediv__(self,z): return asK(z)/self
    def __pow__(self,n):
        assert n>=0
        y=K(1)
        for _ in range(n): y=y*self
        return y

def asK(x): return x if isinstance(x,K) else K(x)
def val(p,x):
    x=Q(x); assert x
    a,b=abs(x.numerator),x.denominator; n=0
    while a%p==0: a//=p; n+=1
    while b%p==0: b//=p; n-=1
    return n
DD=(3-K(0,1))**2
R=(K(1,1),K(0,2))
def double(P):
    x,y=P; z=(3*x*x-DD)/(2*y); X=z*z-2*x
    return X,z*(x-X)-y
def chart(P):
    x,y=P; return 2*y/(x*x+DD),(x**4-6*DD*x*x+DD**2)/(x*x+DD)**2
P2=double(R); P4=double(P2); P8=double(P4)
for m,P in [(1,P4),(2,P8)]:
    uu,vv=chart(P)
    assert vv*vv==1-DD*uu**4
    assert val(2,uu.norm())==7+2*val(2,m)
    assert val(3,uu.norm())==2+2*val(3,m)
    assert val(2,(vv-1).norm())==26+8*val(2,m)
    assert val(3,(vv-1).norm())==8+8*val(3,m)
    for p in [2,3]:
        for c in [uu.re,uu.im,(vv-1).re,(vv-1).im]:
            assert c==0 or val(p,c)>=1+val(p,m)
for e in range(8):
    for m in range(-20,21):
        if m:
            assert val(2,6**e*m)==e+val(2,m)
            assert val(3,6**e*m)==e+val(3,m)
for e in range(8):
    for E in range(e,10):
        for b in [-7,0,5]:
            for m in [-11,0,13]:
                assert b*4*6**E*m==4*6**e*(6**(E-e)*b*m)
# Verify all original indices, not only a finite sample of labels or h.
h=s.symbols('h'); labels=s.symbols('n0:4')
actual=[n*h for n in labels]+[n*(h-1) for n in labels]+[h]
affine=[0]*4+[-n for n in labels]+[0]
slope=list(labels)*2+[1]
assert all(s.expand(actual[j]-affine[j]-slope[j]*h)==0 for j in range(9))
copies=json.loads((HERE/'SOURCE-COPIES.json').read_text())
for name,binding in copies['unchanged_sources'].items():
    assert hashlib.sha256((HERE/(name+'.lean')).read_bytes()).hexdigest()==binding['source_sha256']
assert len(copies['unchanged_sources'])==129
assert set(copies['repaired_sources'])=={'NormalizationInjection318'}
print('PASS: exact duplication, pair arithmetic, oriented translation, 2 actual elliptic indices, coefficient bounds, finite exponent checks, all9 affine source indices,129 unchanged sources and one normalization visibility/base-map repair')
