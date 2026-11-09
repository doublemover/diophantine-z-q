#!/usr/bin/env python3
"""Exact symbolic and finite sanity checks; not Lean or a proof of universality."""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, re
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

def add(P,Q):
    x,y=P; a,b=Q; slope=(b-y)/(a-x); X=slope*slope-x-a
    return X,slope*(x-X)-y
points={1:R,2:P2,4:P4,8:P8,16:double(P8)}
points[20]=add(points[16],points[4])
cert=json.loads((HERE/'entry-certificate.json').read_text())
source=(HERE/'ActualSeventeenEntry318.lean').read_text()
for n,P in points.items():
    x,y=P
    assert y*y==x**3-DD*x
    uu,vv=chart(P)
    assert vv*vv==1-DD*uu**4
    assert cert[str(n)]=={'u':[str(uu.re),str(uu.im)],'v':[str(vv.re),str(vv.im)]}
    for name,coord in [('u',uu),('v',vv)]:
        literal=f'@[expose] def {name}{n} : K := pair ({coord.re.numerator}/{coord.re.denominator}) ({coord.im.numerator}/{coord.im.denominator})'
        assert literal in source
for n,a,b in [(2,1,1),(4,2,2),(8,4,4),(16,8,8),(20,16,4)]:
    u,w=chart(points[a]); a1,b1=chart(points[b]); T=DD*u*u*a1*a1
    un=(u*b1+a1*w)/(1+T)
    vn=(w*b1*(1-T)-2*DD*u*a1*(u*u+a1*a1))/(1+T)**2
    assert (un,vn)==chart(points[n])
u20,v20=chart(points[20]); depths=[val(17,z) for z in [u20.re,u20.im,(v20-1).re,(v20-1).im]]
assert depths==[1,1,4,4]
# Exact second-order error identities, no elliptic equation assumptions needed.
D,u,w,a,b=s.symbols('D u w a b'); T=D*u**2*a**2; den=1+T
SU=(u*b+a*w)/den
SV=(w*b*(1-T)-2*D*u*a*(u**2+a**2))/den**2
EU=u*(b-1)+a*(w-1)-(u+a)*T
EV=(w-1)*(b-1)-T*(w*b+2)-T**2-2*D*u*a*(u**2+a**2)-((w-1)+(b-1))*(2*T+T**2)
assert s.cancel(SU-u-a-EU/den)==0
assert s.cancel(SV-1-(w-1)-(b-1)-EV/den**2)==0
assert (6**2-2)%17==0 and (2*6)%17!=0
for Lf in [1,2,5,17,64]:
    for Lg in [1,3,20,289]:
        for center in [-20,0,64]:
            for m in [-7,0,11]:
                assert center+(Lf*Lg)*m==center+Lf*(Lg*m)==center+Lg*(Lf*m)
for M in [1,64,119]:
    for L2,L3,L17 in [(24,36,340),(4,6,20),(144,216,5780)]:
        L=M*L2*L3*L17
        assert L>0 and all(L%k==0 for k in [M,L2,L3,L17])
        for center in [0,1,64]:
            for m in [-20,0,31]:
                h=center+L*m
                assert all((h-center)%k==0 for k in [M,L2,L3,L17])
expected={
 'ReciprocalChartWitness318':set(range(1,33))|set(range(58,74)),
 'CompressedAnchorWitness318':set(range(33,38))|set(range(74,78)),
 'RealGuardWitness318':set(range(78,90)),
 'PadeRatioWitness318':set(range(90,118)),
 'DetectorGateWitness318':set(range(118,146))}
seen=set()
for name,want in expected.items():
 s=(HERE/(name+'.lean')).read_text(); section=s.split('def fill ',1)[1].split('\n\n',1)[0]
 got=set(map(int,re.findall(r'(?:\|\s*(\d+)\s*=>)',section))) if 'match ' in section else set(map(int,re.findall(r'if i=(\d+)',section)))
 assert got==want,(name,got^want)
 assert not(seen&got)
 seen|=got
assert seen|({0}|set(range(38,58)))==set(range(146))
src=(HERE/'DetectorGateWitness318.lean').read_text()
new=(HERE/'DetectorLocalRegularity318.lean').read_text()
for n in range(118,146):
 expr=re.search(rf'def value{n} \(w : Assignment\) : ℚ := (.*)',src).group(1)
 deps=sorted(set(map(int,re.findall(r'value(\d+)',expr))))
 proof=new.split(f'lemma value{n}_regular',1)[1].split('\n\n',1)[0]
 assert f'unfold value{n}' in proof
 for d in deps:
  assert d<n
  assert f'value{d}_regular p h₀ w hw' in proof
 assert f'have h{n} := value{n}_regular p h₀ w hw' in new

m=json.loads((HERE/'SOURCE-COPIES.json').read_text())
assert len(m['unchanged_sources'])==154 and not m['new_sources']
assert set(m['repaired_sources'])=={'RealOvalNormalization318'}
for name,binding in m['unchanged_sources'].items():
    assert hashlib.sha256((HERE/(name+'.lean')).read_bytes()).hexdigest()==binding['source_sha256']
print('PASS: six actual elliptic/chart certificates, all rational source literals, depths1/1/4/4 at17, two exact second-order errors, Hensel residue6, signed product moduli, all146 coordinates/28 gates,154 exact155r2 copies and original oval instance/parameter repair')

for A in range(2,12):
    for B in range(6):
        residue=2**A*3**B; modulus=6*residue; h0=85*residue
        assert (h0-residue)%modulus==0
        assert h0==20*(17*2**(A-2)*3**B)
        assert val(2,h0)==A and val(3,h0)==B
        for N in range(4):
            for e in range(5):
                for d in [1,2,3,5,17]:
                    label=1+6**(A+B+15)*3**N*20*17**e*d
                    assert label-1==20*17**e*(6**(A+B+15)*3**N*d)
                    assert label>=3 and label%2==1 and label%3==1
for v in range(-50,51):
    e=abs(v)+1
    assert 2*v<2*(2*(e+1))
# Recheck literal actual scalar expression, retaining its29*v(r) factor.
import sympy as sym
r,H,f,I=sym.symbols('r H f I')
packed=(1+(H/r)**2+2*f/r)**2+r*(I/(H*r**15))**2
assert sym.cancel(packed-(1+(H/r)**2+2*f/r)**2-I**2/(H**2*r**29))==0
for name in ['SeventeenScalarDepth318','SeventeenScalarCenter318','ScalarIndexContinuity318','ScalarSmallPrimeProgression318','JointSmallPrimePreparation318']:
    src=(HERE/(name+'.lean')).read_text()
    assert 'set_option maxHeartbeats 1000000' in src
    assert not re.search(r'-/\ninclude [^\n]+ in',src)
    for ns in re.findall(r'^open (.+) \(.+\)$',src,re.M): assert ' ' not in ns
print('PASS: actual85 residue/20R entry identity, preserved2/3 depths, scalar translated-index factorization, label parity/mod3, threshold order, exact29 coefficient, five-source syntax/budget preflight')

source=(HERE/'SmallPrimeFullSource318.lean').read_text()
assert 'p≠2 → p≠3 → p≠17' in source
for token in ['Realization (pre 190)','Realization (pre 241)','Realization (pre 292)',
              'Realization (scalarB (a:ℚ) labels (h:ℤ))',
              'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)',
              'hscalar h hcontinuity','prepared_all_places hglobal a A B (20*17^e*d)']:
    assert token in source,token
for A in range(6,12):
    for B in range(6): assert (6*2**A*3**B)%64==0
for x in [Q(1),Q(-2),Q(3,7)]: assert 1/((-x)**3)==-1/(x**3)
print('PASS: literal full288 consumer object/four actual realizations, support-prime exclusion2/3/17, sameh continuity, retained64, inverse odd-power sign')

import sympy as sp
D,x,y,a,b=sp.symbols('D x y a b')
h=y*y-x**3+D*x
assert sp.expand(4*D**3-(4*D-3*x*x)*(3*x*x-D)**2-27*y**4+27*(y*y+x**3-D*x)*h)==0
assert sp.expand((b-y)*(b+y)-(a-x)*(x*x+x*a+a*a-D)-((b*b-a**3+D*a)-h))==0
assert sp.expand((x*x+x*a+a*a-D)-(3*x*x-D)-(a-x)*(2*x+a))==0
assert sp.expand((y+b)*(b-y)+(x*x+x*a+a*a-D)*(x-a)-((b*b-a**3+D*a)-h))==0
assert sp.expand((x**4-6*D*x*x+D*D)-(x*x+D)**2+8*D*x*x)==0
assert sp.cancel((2*y/(x*x+D))**2-4*x/(x*x+D)**2*(x*x-D)-4*(D*x-x**3+y**2)/(D+x**2)**2)==0
for f in ['LocalDerivativeSeparation318','LocalPointDifference318','CompactLocalPointCoding318','FormalPoleCoherentChart318','ActualSplitOrbitEntry318','GeneralSplitDetectorAccess318','ActualInertOrbitEntry318','AllPrimeSourceProgression318']:
    src=(HERE/(f+'.lean')).read_text()
    assert 'maxHeartbeats 0' not in src
    assert '/--' not in src.split('include hp')[0][-4:]
source=(HERE/'AllPrimeSourceProgression318.lean').read_text()
for token in ['by_cases hs : ∃ x : ZMod p, x^2=2','InertHensel318.square_root_lift',
              'ActualInertOrbitEntry318.error_bounds','by_cases hp : p=2',
              'LocalIndexRegularity318.actual_chart 2 two_error_bound',
              'prepared_progression p (actual_chart p)','finite_preparation',
              'M∣L','∀ i, Prepared (p i) q labels h₀ L (N i) (A i)']:
    assert token in source,token
for vals in [[],[2],[3,7],[4,8,9,17]]:
    J=1
    for x in vals:J*=x
    assert J>0 and all(J%x==0 for x in vals)
print('PASS: exact discriminant/secant/derivative/tangent-chart identities; actual compact coset-cover, split/inert/2 coverage, same original R and positive branch, common finite modulus and all146 source consumer bindings')
