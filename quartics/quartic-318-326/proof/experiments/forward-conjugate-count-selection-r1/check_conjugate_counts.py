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
assert len(m['unchanged_sources'])==222 and len(m['new_sources'])==6
assert not m['repaired_sources']
for name,binding in m['unchanged_sources'].items():
    assert hashlib.sha256((HERE/(name+'.lean')).read_bytes()).hexdigest()==binding['source_sha256']
print('PASS: six actual elliptic/chart certificates, all rational source literals, depths1/1/4/4 at17, two exact second-order errors, Hensel residue6, signed product moduli, all146 coordinates/28 gates,222 exact222r1 copies')

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

for vr in range(-40,41):
    r=abs(vr)+1
    assert vr<2*r
    for vh in range(-30,31):
        target=2*vh+29*vr
        depth=abs(target)+1
        assert target<4*depth
for mods in [[],[2],[3,7],[4,8,9,17]]:
    J=1
    for x in mods:J*=x
    for M in range(1,9):
        h0=64*M*J
        assert h0>0 and h0%64==0 and h0%M==0
        assert all(h0%x==0 for x in mods)
    for A in range(3):
        for B in range(3):
            for d in range(1,5):
                label=1+6**(A+B+15)*3**7*J*d
                assert all((label-1)%x==0 for x in mods)
source=(HERE/'AllPrimePreparedFullSource318.lean').read_text()
for token in ['AllScalarDetectorJoin318.integer_preparation a A B (2^16) M hM',
              'PreparedTwistSource318.current_source_from_twists a labels hn hn1',
              'ActualAnchorAllPlaces318.actual_homogeneous hglobal a A B (2^16) (J*d) hJd',
              'hscalar h hcontinuity','Realization (pre 190)','Realization (pre 241)',
              'Realization (pre 292)','Realization (scalarB (a:ℚ) labels (h:ℤ))',
              'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)']:
    assert token in source,token
assert 'hother' not in source and 'OtherSupport' not in source.split('theorem current_source')[1]
for f in json.loads((HERE/'SOURCE-COPIES.json').read_text())['new_sources']:
    src=(HERE/(f+'.lean')).read_text()
    assert 'maxHeartbeats 0' not in src
    assert 'open scoped' in src or '∏' not in src
support=(HERE/'RationalScalarSupport318.lean').read_text()
assert 'insert 2 (insert 3 (insert 17 q.num.natAbs.primeFactors))' in support
assert 'padicValNat.dvd_of_ne_zero' in support
print('PASS: exact all-support29 valuation choice bounds, finite center/label divisibilities, positive64/M retention, genuine numerator-support coverage binding, fixed2^16 anchor and four literal rational realization consumers, no OtherSupport premise')

from fractions import Fraction as Q
from math import prod
roots=[Q(0),-Q(1,2),-Q(1),Q(1,2399),-Q(32,407)]
assert len(set(roots))==5
for scales in [[Q(1),Q(2),Q(3)],[Q(1),-Q(5,7),Q(11,13)],[Q(1),Q(1),-Q(1)]]:
    slopes=[-theta/c**2 for c in scales for theta in roots]
    D=prod(a.denominator for a in slopes)
    coeff=[int(a*D**2) for a in slopes]
    assert D>0 and all(Q(k)==a*D**2 for k,a in zip(coeff,slopes))
    assert all((coeff[i]==coeff[j])==(slopes[i]==slopes[j]) for i in range(15) for j in range(15))
    merged=set(coeff)
    for j,c in enumerate(scales):
        assert len(set(coeff[5*j:5*j+5]))==5
        for u,w in [(23,1),(-41,7),(31,-3),(101,13)]:
            t=Q(u,(D*w)**2)
            vals=[u+k*w*w for k in coeff[5*j:5*j+5]]
            actual=prod(c*c*t-theta for theta in roots)
            assert actual==prod(vals)*Q(c,D*w)**10
            for sf in [Q(7,11),-Q(19,3)]:
                assert actual*sf**2==prod(vals)*(Q(c,D*w)**5*sf)**2
            for i in range(5):
                for k in range(5):
                    assert vals[i]-vals[k]==(coeff[5*j+i]-coeff[5*j+k])*w*w
            assert all(coeff[5*j+i] in merged for i in range(5))
import sympy as sp
c,u,z=sp.symbols('c u z',nonzero=True)
theta=[sp.Rational(x.numerator,x.denominator) for x in roots]
assert sp.factor(sp.prod(c*c*u/z**2-x for x in theta)-sp.prod(u-x/c**2*z**2 for x in theta)*(c/z)**10)==0
src=(HERE/'ContactPrimeFullSource318.lean').read_text()
for token in ['let C := construct labels','threshold≤parameter C u w',
              'let Pi := MergedContactPrimePattern318.product C u w','Nat.ModEq (Pi^3*Mminus) h 0',
              'AllScalarSupportPreparation318.Prepared a labels h',
              'pre (190+51*j.val)=(rowProduct C u w j:ℚ)*z^2',
              'Realization (pre 190)','Realization (pre 241)','Realization (pre 292)',
              'Realization (scalarB (a:ℚ) labels (h:ℤ))',
              'HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)']:
    assert token in src,token
assert src.index('let C := construct labels')<src.index('∃ threshold')<src.index('∀ u w : ℤ')<src.index('∃ h : ℕ')
print('PASS: exact fifteen integer forms, denominator clearing, all duplicate merges, five-distinct rows, contact tenth powers, original squarefactor fifth powers, signed scales/w, source190/241/292 and same-h full288 binding')

def vp(p,n):
    assert n
    n=abs(n);v=0
    while n%p==0:v+=1;n//=p
    return v
primes=[n for n in range(409,50000,408) if sp.isprime(n)][:5]
assert len(primes)==5
N=prod(primes)
for p0 in list(sp.primerange(2,200))+primes:
    assert (vp(p0,N)>0)==(p0 in primes)
for k in range(-25,26):
    z=1+408*k
    for p0 in [2,3,17]:assert vp(p0,z)==0
    assert z==1+8*(51*k)==1+3*(136*k)==1+17*(24*k)
assert Q(1,8)<Q(1,4) and Q(1,3)<1 and Q(1,17)<1
for ns in [(-7,-2,-13),(0,0,0),(3,1,2),(11,7,5)]:
    mod=2**abs(ns[0])*3**abs(ns[1])*17**abs(ns[2])
    assert mod>0
    for D in [1,6,35,2399]:
        for w in [mod,-mod,7*mod,17*mod]:
            assert all(vp(p0,D*w)>=n for p0,n in zip([2,3,17],ns))
for a,b in [(1,408),(13,2**7*3**5*17**3),(N,408)]:
    z=Q(a,b);pole=N*z*z
    assert all(vp(p0,z.numerator)-vp(p0,z.denominator)>=0 for p0 in primes)
    assert sp.integer_nthroot(pole.denominator,2)[1]
# Without the selected-place squarefactor condition the conclusion is false.
bad=Q(N,primes[0]**2)
assert not sp.integer_nthroot(bad.denominator,2)[1]
src=(HERE/'SelectedPoleFullSource318.lean').read_text()
for token in ['∃ threshold : ℚ, ∃ Q : ℕ, 0<Q','(Q:ℤ)∣w',
              '(408:ℤ)∣value u w k-1','SelectedContactDenominators318.SelectedTrace',
              'ThreeSelectedPolePreparation318.Prepared','hfamily u w hp hw hray h hcontinuity hpoles',
              'Realization (pre 190)','Realization (pre 241)','Realization (pre 292)',
              'Realization (scalarB (a:ℚ) labels (h:ℤ))']:
    assert token in src,token
assert src.index('∃ Q : ℕ')<src.index('∀ u w : ℤ')<src.index('∃ h : ℕ')
prep=(HERE/'ThreeSelectedPolePreparation318.lean').read_text()
for token in ['IsSquare b.den','3≤padicValRat 2 b','1≤padicValRat 3 b','2≤padicValRat 17 b']:
    assert token in prep
print('PASS: exhaustive row support of five ray primes, exact408 shapes/units, strict Hensel bounds, positive prior denominator modulus including signed/negative thresholds, necessary support condition counterexample, all3 actual preparation inputs and unchanged four Realizations')

# Exact curve identity and valuation improvement, including signed coordinates.
u,y,D=sp.symbols('u y D')
assert sp.expand((y-1)*(y+1)+D*u**4)==y*y-1+D*u**4
for p0 in [3,5,7,17,41]:
    for r in range(1,6):
        for sign in [-1,1]:
            u0=sign*p0**r;y0=1+p0**(4*r)
            d0=Q(1-y0*y0,u0**4)
            assert y0*y0==1-d0*u0**4
            assert vp(p0,d0.numerator)-vp(p0,d0.denominator)==0
            assert vp(p0,y0+1)==0 and vp(p0,y0-1)==4*r
# Primary Pi^3 factor and signed labels; opposite h-1, not h+1.
for p0 in [3,7,17,41]:
    for M in [1,2,15,64]:
        for k in [1,5,17]:
            Pi=p0*k
            for m0 in [0,1,7]:
                h=Pi**3*M*m0
                for n in [-19,-1,0,1,23]:assert n*h==p0**3*M*(n*k**3*m0)
        for m0 in [0,1,19]:
            h=1+M*m0
            for n in [-19,-1,0,1,23]:assert n*(h-1)==(n*m0)*M
from math import gcd
for N in range(1,50):
    for a in range(N):
        order=N//gcd(N,a)
        assert order>0
        for M in range(100):assert (M*a%N==0)==(M%order==0)
sources={n:(HERE/(n+'.lean')).read_text() for n in ['SelectedFormalEntry318','SelectedPositiveDelta318','SelectedQuotientOrders318','AllSelectedChartDepths318']}
assert '((M:ℤ) • R)' in sources['SelectedFormalEntry318']
assert 'Nat.modEq_iff_dvd.mp hh.symm' in sources['SelectedFormalEntry318']
assert 'p^3*M∣Pi^3*M' in sources['SelectedFormalEntry318']
assert 'CompactLocalPointCoding318.finite_formal_quotient' in sources['SelectedQuotientOrders318']
assert 'ShortCurveBaseChange318.pointMap' in sources['SelectedQuotientOrders318']
assert 'addOrderOf (generator p rho hr)' in sources['SelectedQuotientOrders318']
assert '∀ j : Fin 3, ∀ i : Fin 5' in sources['AllSelectedChartDepths318']
assert '∀ n : ℤ' in sources['AllSelectedChartDepths318']
assert 'selected_divides C u w (j,i)' in sources['AllSelectedChartDepths318']
assert 'SelectedQuotientOrders318.order p (-rho)' in sources['AllSelectedChartDepths318']
print('PASS: exact curve factor identity and odd-prime delta precision, Pi^3 and signed h-1 index transport, finite cyclic order divisibility controls, literal half-point and all15 selected positions; numerical controls are not Lean proofs')
# Every prefix identity preserves the original proof body and narrows only
# the constructed row domain. This checks exact text, not a proof of Lean.
raw_dir=HERE.parents[1]/'progress'
raw=(raw_dir/'RawDetector318.lean').read_text()
rec=(raw_dir/'RawReciprocal318.lean').read_text()
prefix=(HERE/'PrefixDetectorLeaves318.lean').read_text()
for name,src in [(f'leaf{i}_square',raw) for i in [0,1,2,3,4,5,10,11,12,13,14,15]]+[(f'{tag}_{s}',rec) for tag in ['VA','VS','VT','VZ'] for s in ['curve_conjugate','linear_leaf_even']]:
    old=src.split('theorem '+name,1)[1].split('\n\n',1)[0]
    new=prefix.split('theorem '+name,1)[1].split('\n\n',1)[0]
    new=new.replace('Constraints ((stage0 S).take 107) w','Constraints (stage0 S) w').replace('(l:=(stage0 S).take 107)','(l:=stage0 S)').replace('[List.length_take,stage0,List.length_cons,List.length_nil]','[stage0,List.length_cons,List.length_nil]')
    assert new==old,name
    rows=[int(x) for x in re.findall(r'\(n:=(\d+)\)',new)]
    assert all(i<107 for i in rows)
# Independently evaluate every original quadratic gate used by the twelve
# square leaves and compare literal real/imaginary pairs to the square.
x={i:sp.Symbol(f'w{i}') for i in range(146)}
def expr(s):
    s=re.sub(r'\s*:\s*ℚ','',s).replace('^','**')
    s=re.sub(r'\(value(\d+) w\)',lambda m:f'V{m[1]}',s)
    s=re.sub(r'w (\d+)',lambda m:f'w{m[1]}',s)
    return sp.sympify(s,locals={**{f'w{i}':a for i,a in x.items()},**{f'V{i}':a for i,a in vals.items()}},rational=True)
vals={}
subs={x[58]:x[1]**2+2*x[2]**2,x[59]:x[1]*x[2],x[60]:x[5]**2+2*x[6]**2,x[61]:x[5]*x[6],x[62]:x[10]**2+x[9]**2/2,x[63]:x[9]*x[10],x[64]:x[13]**2+2*x[14]**2,x[65]:x[13]*x[14],x[90]:x[76]**2+2*x[77]**2,x[91]:x[76]*x[77]}
gate=(HERE/'DetectorGateWitness318.lean').read_text()
for i in range(118,146):
    body=re.search(rf'def value{i} \(w : Assignment\) : ℚ := (.*)',gate).group(1)
    vals[i]=expr(body).xreplace(subs)
    subs[x[i]]=vals[i]
def pair_args(s):
    s=s.split('pair ',1)[1];out=[];depth=0;start=None
    for j,c in enumerate(s):
        if c=='(':
            if depth==0:start=j
            depth+=1
        elif c==')':
            depth-=1
            if depth==0:
                out.append(s[start:j+1])
                if len(out)==2:return out
    raise ValueError(s)
for i in [0,1,2,3,4,5,10,11,12,13,14,15]:
    leaf=re.search(rf'def leaf{i} \(S : ℚ\) \(w : Assignment\) : K := (.*)',raw).group(1)
    test=re.search(rf'def test{i} \(S : ℚ\) \(w : Assignment\) : K := (.*)',raw).group(1)
    a,b=[expr(s).xreplace(subs) for s in pair_args(leaf)]
    c,d=[expr(s).xreplace(subs) for s in pair_args(test)]
    assert sp.expand(a-c*c-2*d*d)==0,i
    assert sp.expand(b-2*c*d)==0,i
# Generic conjugated curve and actual positive weighted valuation margins.
a,b,c,d=sp.symbols('a b c d')
def mul(z,w):return (sp.expand(z[0]*w[0]+2*z[1]*w[1]),sp.expand(z[0]*w[1]+z[1]*w[0]))
def power(z,n):
    ans=(sp.Integer(1),sp.Integer(0))
    for _ in range(n):ans=mul(ans,z)
    return ans
U=(a,b);V=(c,d);co=(11,-6)
orig=tuple(sp.expand(z) for z in (power(V,2)[0]-1+mul(co,power(U,4))[0],power(V,2)[1]+mul(co,power(U,4))[1]))
conj=tuple(sp.expand(z) for z in (power((c,-d),2)[0]-1+mul((11,6),power((a,-b),4))[0],power((c,-d),2)[1]+mul((11,6),power((a,-b),4))[1]))
assert conj==(orig[0],-orig[1])
assert 11*11-2*6*6==49
for m in [1,4,13]:assert -(2*m-1)+2*m==1
assert -1+4==3 and -1+2*4==7
assert -1+2*2==3
# Original five contact constants, all original large-prime rays safely
# exceed their finite numerator/denominator data. Check all three weights.
def vq(p,z):
    z=Q(z)
    return vp(p,z.numerator)-vp(p,z.denominator)
for p0 in [int(sp.nextprime(76176)),int(sp.nextprime(100000)),int(sp.nextprime(200000))]:
    for root in roots:
        assert vq(p0,root-1)==0
        for scale in [-3,-1,1,2]:
            parameter=root+p0
            delta=parameter-1
            contact=prod(parameter-r for r in roots)
            w1=Q(scale)**10*delta**2/contact
            assert vq(p0,contact)==1 and vq(p0,delta)==0
            assert [vq(p0,w1),vq(p0,w1**7*delta**18),vq(p0,w1**25*delta**72)]==[-1,-7,-25]
# Fixed all15/same-root/index boundaries and exact residual tests.
remaining=(HERE/'ConstructedPrimaryDepths318.lean').read_text().split('@[expose] def Remaining',1)[1].split('\n\n',1)[0]
for idx,depth in [(0,4),(5,2),(10,4),(11,13),(12,13),(13,13),(14,4),(15,13)]:
    assert f'Bound v {depth} (test{idx} 0 w)' in remaining
final=(HERE/'SelectedTraceFromDepths318.lean').read_text()
for t in ['∀ j : Fin 3, ∀ i : Fin 5','SelectedQuotientOrders318.order p rho hr∣Mminus','SelectedQuotientOrders318.order p (-rho)','ConstructedPrimaryDepths318.Remaining (place p rho hr)','(h:ℤ) u w hp','(190+51*j.val)','DetectorGateWitness318.witness_first107','Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0']:
    assert t in final,t
assert 'Constraints (stage0' not in final
print('PASS: all20 original leaf/curve proofs narrowed exactly to constructed107 prefix, independent12 square identities, all4 conjugated curve equations, norm49, exact three negative odd weights, selected five-contact delta units, positive8 chart leaf margins and eight explicit remaining same-root tests')
# Exact original index1 reciprocal chart, coefficient and norm identities.
sqrt2=sp.sqrt(2)
u1=(8+14*sqrt2)/41;v1=(207-960*sqrt2)/1681;D=11-6*sqrt2
assert sp.expand(v1*v1-(1-D*u1**4))==0
assert sp.expand(u1*u1.xreplace({sqrt2:-sqrt2}))==-sp.Rational(8,41)
# Translation denominator unit mechanism: near identity plus integral chart.
for p0 in [int(sp.nextprime(76176)),int(sp.nextprime(100000))]:
    for r in [1,2,4]:
        for sign in [-1,1]:
            a=sign*p0**r;b=1+p0**(4*r);d=Q(1-b*b,a**4)
            assert vq(p0,d)==0
            for u0,w0 in [(Q(2),Q(3)),(Q(-8,41),Q(207,1681)),(Q(14,41),Q(-960,1681))]:
                T=d*u0*u0*a*a;den=1+T
                result=(u0*b+a*w0)/den
                assert vq(p0,T)>=2 and vq(p0,den)==0 and vq(p0,result)>=0
# Compression orientation and the actual norm of the square.
a,b,c,d=sp.symbols('a b c d')
z=mul((a,b),(c,d));f=power(z,2)
assert sp.expand(f[0]**2-2*f[1]**2-(z[0]**2-2*z[1]**2)**2)==0
assert sp.expand((-z[0])**2-2*(-z[1])**2-(z[0]**2-2*z[1]**2))==0
for vprimary in range(4,12):
    for vopp in range(5):assert vprimary+vopp>=4
for vprimary in range(5):
    for vopp in range(1,12):assert 2*(vprimary+vopp)>=2
comp=(HERE/'SelectedSixComparisonTrace318.lean').read_text()
section=comp.split('@[expose] def Comparisons',1)[1].split('\n\n',1)[0]
for idx,depth in [(10,4),(11,13),(12,13),(13,13),(14,4),(15,13)]:assert f'Bound v {depth} (test{idx} 0 w)' in section
assert 'test0 ' not in section and 'test5 ' not in section
for token in ['SelectedNormTestValues318.norm_tests','hn.1,hn.2,hcomp','(190+51*j.val)','SelectedContactDenominators318.SelectedTrace']:
    assert token in comp
normsrc=(HERE/'SelectedNormTestValues318.lean').read_text()
for token in ['test0 0 (DetectorGateWitness318.witness','test5 0 (DetectorGateWitness318.witness','ScalarTranslatedIndex318.shifted_chart h hh','AnchorNorm318.norm_pow','norm_bound p rho hr (chartU h) 4 0','norm_bound p rho hr (chartU (h-1)) 0 1']:
    assert token in normsrc,token
log=(HERE/'ActualOrientedLogMembership318.lean').read_text()
for token in ['(u/(p:ℚ_[p])).lift hquot','CanonicalRoot318.root_unique','ClosedScaledEvaluation318.valueV_near_one','CoherentAdditionV318.reciprocal_chart_point n','(j*n)=j • mappedPoint','ActualLogIsometry318.logHom_zero_iff','(j • Q).val=mappedPoint p rho hr (j*n)','logHom p hp _ _ (j • Q)/logHom p hp _ _ Q=(j:ℚ_[p])']:
    assert token in log,token
last=(HERE/'SelectedActualLogRatios318.lean').read_text()
for token in ['Nat.ModEq (Pi^3*Mminus) h 0','Nat.ModEq Mplus h 1','LogarithmicOrbit p hp rho hr (h:ℤ)','LogarithmicOrbit p hp (-rho) (negative_root p rho hr) ((h:ℤ)-1)']:
    assert token in last,token
assert sp.cancel(sp.Symbol('j')*sp.Symbol('L',nonzero=True)/sp.Symbol('L',nonzero=True)-sp.Symbol('j'))==0
print('PASS: exact original index1 curve/norm, integral translation denominator and signed rational samples, compressed h-1 norm-square identity, produced norm depths4/2, six remaining comparisons, actual analytic subgroup/root binding, same mapped signed multiples and both CRT integer-log families')
# Exact original translated ordinate and compressed source common parameter.
u,v,k,m,D=sp.symbols('u v k m D')
shift=(k*v/u-m)/(k*k+D*u*u)
B=k*k+m*shift+D*u*u*shift*shift
Vminus=(v*m/k**2*(1-D*u*u/k**2)+2*D*u/k*(u*u+1/k**2))/(1+D*u*u/k**2)**2
num=sp.together(Vminus-u*B/k).as_numer_denom()[0]
assert sp.reduced(num,[v*v-(1-D*u**4),m*m-(k**4-D)],v,m,k,D,u)[1]==0
nU,nV,G=sp.symbols('nU nV G')
assert sp.cancel(nU*(k*v/u)/(k*nV)-((-nU/nV)/(-u/v)))==0
assert sp.cancel(k*shift/B*G-(-(-u*shift)/(u*B/k))*G)==0
assert sp.expand(D*(u*u*shift*shift)**2-D*(-u*shift)**4)==0
# The actual source test polynomials, evaluated from the literal gate bodies.
primary=[(x[102+4*j],x[103+4*j]) for j in range(4)]
alternate=[(x[104+4*j],x[105+4*j]) for j in range(4)]
for j in range(4):
    t=re.search(rf'def test{10+j} \(S : ℚ\) \(w : Assignment\) : K := (.*)',raw).group(1)
    actual=[expr(z).xreplace(subs) for z in pair_args(t)]
    assert sp.expand(actual[0]-primary[j][0]+alternate[j][0])==0
    assert sp.expand(actual[1]-primary[j][1]-alternate[j][1])==0
t=re.search(r'def test14 \(S : ℚ\) \(w : Assignment\) : K := (.*)',raw).group(1)
actual=[expr(z).xreplace(subs) for z in pair_args(t)]
assert sp.expand(actual[0]-primary[0][0]+3723*(2*x[0]+1)**2)==0
assert sp.expand(actual[1]-primary[0][1])==0
S,T,Z=primary[1:]
Sm=(S[0]-2,S[1])
polyT=power(T,2);polySTZ=mul(mul(mul(S,Sm),T),Z);polySZ=mul(power(Sm,2),power(Z,2))
poly=(polyT[0]-polySTZ[0]+polySZ[0]-1,polyT[1]-polySTZ[1]+polySZ[1])
t=re.search(r'def test15 \(S : ℚ\) \(w : Assignment\) : K := (.*)',raw).group(1)
actual=[expr(z).xreplace(subs) for z in pair_args(t)]
assert all(sp.expand(a-b)==0 for a,b in zip(actual,poly))
# Analytic rate arithmetic and quotient cancellation, not convergence proof.
for r in range(1,13):
    for s in range(1,13):
        assert min(8*r,16*s)>=8 and min(16*r,16*s)>=16
        if r>=4 and s>=4:assert 4*min(r,s)>=16
u,v,b,J,G=sp.symbols('u v b J G',nonzero=True)
assert sp.cancel(((-u/v)/b)*(v*J/G)-(-u*J)/(b*G))==0
for e in [0,1,2,3,4]:
    for f in [0,1,2,3,4]:
        assert min(16+e,16+f)>=16
# Actual order interface has no residue-test or local log membership inputs.
final=(HERE/'SelectedTraceFromOrders318.lean').read_text()
interface=final.split('@[expose] def Orders',1)[1].split('\n\n',1)[0]
assert '∀ j : Fin 3, ∀ i : Fin 5' in interface
assert interface.count('SelectedQuotientOrders318.order')==2
assert all(t not in interface for t in ['Comparisons','Bound','SelectedTrace','logHom','Constraints'])
for t in ['ActualAlternateRatioPrecision318.selected','ActualSixComparisonValues318.comparisons','FixedArithmeticLabels318.detector_relations','(190+51*j.val)','Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*Mminus) h 0']:
    assert t in final,t
for f in json.loads((HERE/'SOURCE-COPIES.json').read_text())['new_sources']:
    src=(HERE/(f+'.lean')).read_text()
    assert 'set_option maxHeartbeats 1000000' in src
    assert not re.search(r'(?<![.\w])map_div\b',src)
print('PASS: exact oriented translated ordinate modulo both original curve equations; primary z-ratio and original common G denominator; all six literal comparison/beta/Lucas polynomials; mixed8/16 and primary16 rates; quotient cancellation; order-only all15 interface and same stored poles; 222 exact222r1 copies')
# New connected order-modulus span: these finite checks are NOT existence proofs.
from math import gcd,lcm
from fractions import Fraction
from itertools import product as cartesian
count=0
for ww in range(-15,16):
 for uu in range(-30,101):
  vals=[uu+k*ww*ww for k in range(-3,7)]
  primes=[v for v in vals if sp.isprime(v)]
  for pp in primes:
   for qq in primes:
    if pp!=qq:
     assert gcd(pp,ww)==1
     count+=1
assert count>1000
# Exact coefficient difference used by the original source proof.
ci,cj,uu,ww=sp.symbols('ci cj uu ww')
assert sp.expand((uu+ci*ww**2)-(uu+cj*ww**2)-(ci-cj)*ww*ww)==0
# Bound uses only fixed denominators/numerators, not the later variable w.
for D in [1,2,17,2399,407*2399]:
 for cs in [[Fraction(1),Fraction(3,7),Fraction(-41,23)], [Fraction(11,17),Fraction(9),Fraction(2,3)]]:
  bound=76176+D+sum(abs(c.numerator)+c.denominator for c in cs)
  pp=int(sp.nextprime(bound))
  assert pp>76176 and pp>D and all(pp>abs(c.numerator) and pp>c.denominator for c in cs)
  assert gcd(pp,D)==1 and all(gcd(pp,c.numerator*c.denominator)==1 for c in cs)
# All original15 positions survive duplicate local orders.
positions=list(cartesian(range(3),range(5)))
assert len(positions)==15
for shift in range(1,20):
 orders=[1+(i+2*j+shift)%11 for i,j in positions]
 actual=lcm(*orders)
 assert actual>0 and all(actual%x==0 for x in orders)
 for multiple in [actual,3*actual,17*actual]:
  assert all(multiple%x==0 for x in orders) and multiple%actual==0
# LCM construction alone does not imply simultaneous residue0/residue1 access.
assert not any(h%2==0 and h%2==1 for h in range(20))
# Residue square and strict-unit-derivative Hensel corrections through p^4.
roots_checked=0
for pp in list(sp.primerange(3,500)):
 if pp%8!=1:continue
 roots=[x for x in range(pp) if (x*x-2)%pp==0]
 assert len(roots)==2 and roots[0]==pp-roots[1]
 for rr in roots:
  assert gcd(2*rr,pp)==1
  modulus=pp
  for depth in range(1,4):
   correction=(-(rr*rr-2)//modulus*pow(2*rr,-1,pp))%pp
   rr+=correction*modulus
   modulus*=pp
   assert (rr*rr-2)%modulus==0 and gcd(2*rr,pp)==1
  roots_checked+=1
assert roots_checked>20
for zz in range(1,10000,408):assert zz%8==1
# Source joins retain actual objects, previous thresholds, orientation and CRT.
unit=(HERE/'SelectedVariableDenominatorUnit318.lean').read_text()
assert 'row_distinct C hn' in unit and 'C.coefficient (j,i)-C.coefficient (j,l)' in unit
bound=(HERE/'FixedSelectedPrimeBound318.lean').read_text()
bound_body=bound.split('@[expose] def bound',1)[1].split('\n\n',1)[0]
assert 'w' not in bound_body and 'C.denominator' in bound_body and '.num.natAbs' in bound_body and '.den' in bound_body
mod=(HERE/'ActualSelectedOrderModuli318.lean').read_text()
for tok in ['Fin 3 × Fin 5','Finset.univ.lcm (primaryOrder','Finset.univ.lcm (oppositeOrder','Finset.lcm_ne_zero_iff','Finset.dvd_lcm','Finset.lcm_dvd','negative_root p (r i).val']:
 assert tok in mod,tok
ray=(HERE/'SelectedRayEmbeddings318.lean').read_text()
for tok in ['ZMod.exists_sq_eq_two_iff hp2','ZMod.intCast_zmod_eq_zero_iff_dvd','PadicInt.norm_intCast_lt_one_iff','PadicInt.norm_natCast_eq_one_iff','ScalarLocalSquares318.square_of_near_square','sq_eq_sq_iff_eq_or_eq_neg','theorem all_orientations','theorem ray_preparation_family','(190+51*j.val)','Nat.ModEq L h h₀','Nat.ModEq (plus C u w hp r) h 1']:
 assert tok in ray,tok
assert '∀ r : Roots' not in ray.split('theorem ray_preparation_family',1)[1]
assert '∀ s : Fin 3 × Fin 5 → Bool' in ray.split('theorem ray_preparation_family',1)[1]
print(f'PASS: {count} distinct-prime/w-unit finite cases; exact difference polynomial; prior fixed rational exclusions; actual15-position lcm arithmetic with explicit CRT negative control; {roots_checked} unit-derivative lifts through p^4; all root orientations and same literal three-pole consumer;222 exact222r1 copies')
# Actual good reduction: both simple-root charts, exact residual preservation.
chart_counts=[0,0]
for pp in list(sp.primerange(3,32)):
 for dd in range(1,pp):
  for xx in range(pp):
   for yy in range(pp):
    if (yy*yy-xx**3+dd*xx)%pp:continue
    dy=2*yy%pp;dx=(3*xx*xx-dd)%pp
    assert dy or dx
    use_y=bool(dy);chart_counts[0 if use_y else 1]+=1
    a=yy if use_y else xx;modulus=pp
    for depth in range(1,3):
     f=a*a-xx**3+dd*xx if use_y else a**3-dd*a-yy*yy
     df=2*a if use_y else 3*a*a-dd
     assert f%modulus==0 and df%pp!=0
     a+=(-(f//modulus)*pow(df,-1,pp)%pp)*modulus
     modulus*=pp
    xxx,yyy=(xx,a) if use_y else (a,yy)
    assert (yyy*yyy-xxx**3+dd*xxx)%modulus==0
    assert xxx%pp==xx and yyy%pp==yy
assert all(n>100 for n in chart_counts)
# Exact smoothness discriminant and alternative secant polynomial.
d,x,y,a,b=sp.symbols('d x y a b')
curve=y*y-x**3+d*x
assert sp.expand(4*d**3-(4*d-3*x*x)*(3*x*x-d)**2-27*y**4+27*(y*y+x**3-d*x)*curve)==0
c1=y*y-x**3+d*x;c2=b*b-a**3+d*a
assert sp.expand((b-y)*(b+y)-(a-x)*(x*x+x*a+a*a-d)-(c2-c1))==0
# Independent literal finite-curve point counts and original R orders.
def add(P,Q,p,D):
 if P is None:return Q
 if Q is None:return P
 x,y=P;u,v=Q
 if x==u and (y+v)%p==0:return None
 m=((v-y)*pow((u-x)%p,-1,p) if x!=u else (3*x*x-D)*pow(2*y,-1,p))%p
 xx=(m*m-x-u)%p;yy=(m*(x-xx)-y)%p
 return xx,yy
order_tests=[];quarter_failures=[]
for pp in [17,41,73,89,97,113]:
 for rr in range(pp):
  if rr*rr%pp!=2:continue
  dd=(3-rr)**2%pp
  assert dd
  points=[(x,y) for x in range(pp) for y in range(pp) if (y*y-x*x*x+dd*x)%pp==0]
  R=((1+rr)%pp,2*rr%pp);assert R in points
  count=len(points)+1;P=None
  for n in range(1,count+1):
   P=add(P,R,pp,dd)
   if P is None:break
  assert P is None and count%n==0
  order_tests.append((pp,rr,count,n))
  if (count//4)%n:quarter_failures.append((pp,rr,count,n))
assert len(order_tests)==12
# Deliberately do NOT assert count/4: it needs additional original ray/halving input.
print('FINITE_ORIGINAL_ORDER_DATA',order_tests)
print('FULL_COUNT_ONLY_NEGATIVE_CONTROLS',quarter_failures)
res=(HERE/'GoodReductionResidue318.lean').read_text()
for tok in ['PadicInt.ker_toZMod','PadicInt.maximalIdeal_eq_span_p','hensels_lemma hnear','residue_equal p b a','3*x^2-D']:
 assert tok in res,tok
lift=(HERE/'GoodReductionLifting318.lean').read_text()
for tok in ['X^2-C (x^3-D*x)','X^3-C D*X-C (y^2)','hensel_same_residue p F y','hensel_same_residue p F x','LocalPointDifference318.close_points']:
 assert tok in lift,tok
sep=(HERE/'IntegralFormalSeparation318.lean').read_text()
for tok in ['Point.add_self_of_Y_ne','difference_x','alternative_slope','point','hsep']:
 if tok!='point':assert tok in sep,tok
card=(HERE/'GoodReductionCardinality318.lean').read_text()
for tok in ['theorem same_coset_residue','theorem code_injective','theorem code_surjective','Equiv.ofBijective','Point.some_ne_zero','1+Nat.card (ResidueCurve p D)']:
 assert tok in card,tok
last=(HERE/'SelectedReductionOrder318.lean').read_text()
for tok in ['SelectedQuotientOrders318.subgroup','SelectedQuotientOrders318.generator','addOrderOf_dvd_natCard','(3-residueRoot p rho hr)^2','actual_moduli_dvd_counts','Finset.dvd_lcm']:
 assert tok in last,tok
print(f'PASS: both genuine Hensel coordinate charts sampled {chart_counts}, residue-preserving lifts through p^3; exact derivative/secant identities;12 original finite-curve R orders divide full counts; actual formal quotient bijection and15-position LCM consumers;222 exact222r1 copies')
# Four actual2-torsion subgroup and quotient-index mechanism in finite groups.
four_cases=0
for aa in range(1,8):
 for bb in range(1,8):
  tors={(0,0),(aa,0),(0,bb),(aa,bb)}
  assert len(tors)==4
  for x in tors:
   assert ((2*x[0])%(2*aa),(2*x[1])%(2*bb))==(0,0)
   for y in tors:assert ((x[0]+y[0])%(2*aa),(x[1]+y[1])%(2*bb)) in tors
  for x in range(2*aa):
   for y in range(2*bb):
    order=lcm((2*aa)//gcd(2*x,2*aa),(2*bb)//gcd(2*y,2*bb))
    assert (aa*bb)%order==0
    four_cases+=1
# Actual historical branch certificate and original R, for all admissible
# finite root data in this sample; these are not prime-pattern existence proofs.
quarter_examples=[]
for pp in list(sp.primerange(17,600)):
 zs=[z for z in range(pp) if pow(z,8,pp)==pp-1]
 ts=[t for t in range(pp) if pow(t,4,pp)==2]
 if not zs or not ts:continue
 for rho in range(pp):
  if rho*rho%pp!=2:continue
  eps=(1+rho)%pp
  epsroots=[a for a in range(pp) if a*a%pp==eps]
  assert epsroots and eps
  dd=(3-rho)**2%pp
  for a in epsroots:
   u=(a+rho*pow(a,-1,pp))%pp
   x=(1+2*rho-2*u)%pp
   y=(-2+10*rho-(rho+4)*u)%pp
   mm=(2-u)%pp
   assert y and (y*y-x**3+dd*x)%pp==0
   assert (2*y*mm-3*x*x+dd)%pp==0
   assert (mm*mm-2*x-1-rho)%pp==0
   assert (mm*(x-1-rho)-y-2*rho)%pp==0
   assert add((x,y),(x,y),pp,dd)==((1+rho)%pp,2*rho%pp)
  count=1+sum((y*y-x**3+dd*x)%pp==0 for x in range(pp) for y in range(pp))
  R=((1+rho)%pp,2*rho%pp);P=None
  for n in range(1,count+1):
   P=add(P,R,pp,dd)
   if P is None:break
  assert count%4==0 and (count//4)%n==0
  quarter_examples.append((pp,rho,count,n))
assert len(quarter_examples)>=6
assert not any(pow(t,4,17)==2 for t in range(17))
print('ACTUAL_QUARTER_ORDER_DATA',quarter_examples)
# Confirm actual source identity and branch/quotient/cardinality consumers.
four=(HERE/'FourTorsionQuotient318.lean').read_text()
for tok in ['x=0 ∨ x=A ∨ x=B ∨ x=A+B','Nat.card (subgroup A B hA hB)=4','H.card_mul_index','addOrderOf_dvd_natCard (q Q)','twice_mem_zero','Nat.card G/4']:
 assert tok in four,tok
actual=(HERE/'ActualFourTorsion318.lean').read_text()
for tok in ['zeroRoot','positiveRoot','same_coset_residue','point_nonformal','Finite.of_equiv','double_order_dvd_quarter']:
 assert tok in actual,tok
lifting=(HERE/'SelectedEpsilonLift318.lean').read_text()
assert 'BranchHalving.epsilon_square_from_roots' in lifting and 'hensel_same_residue p F a hF hd' in lifting
half=(HERE/'ActualHalfPointLift318.lean').read_text()
for tok in ['BranchHalving.explicit_half','Point.add_self_of_Y_ne','ShortCurveBaseChange318.pointMap_some','GlobalGeneratorPoints318.R','Q+Q=']:
 assert tok in half,tok
last=(HERE/'SelectedQuarterOrder318.lean').read_text()
for tok in ['ActualHalfPointLift318.original_half','ActualFourTorsion318.doubled_order_dvd_quarter_of_square','SelectedQuotientOrders318.order','pointCount p rho hr/4','Fin 3 × Fin 5','negative_root p','counts C u w hv r false i/4','counts C u w hv r true i/4']:
 assert tok in last,tok
print(f'PASS: {four_cases} finite double/quarter cases;{len(quarter_examples)} original R quarter orders with explicit extra root data; literal halving coordinates/sign; actual formal quotient torsion and all15 quarter-LCM consumers;222 exact222r1 copies')

# Signed Gaussian ray: exact original norm, both absolute-value Jacobi
# denominators, both quadratic residues, Euler quartic condition and roots.
ray_cases=[];signed_cases=set();small_root_cases=[]
for aa in range(-247,250,16):
 for bb in range(-240,241,16):
  pp=aa*aa+bb*bb
  if not sp.isprime(pp):continue
  assert aa%16==9 and bb%16==0 and pp%16==1
  q1,q2=abs(aa),abs(aa+bb)
  assert 0<q1<pp and 0<q2<pp and q1%2==q2%2==1
  assert q1%8 in (1,7) and q2%8 in (1,7)
  assert gcd(pp,q1)==gcd(pp,q2)==1
  assert (bb*bb-pp)%q1==0
  assert ((aa-bb)**2-2*pp)%q2==0
  assert int(sp.jacobi_symbol(pp,q1))==int(sp.jacobi_symbol(bb,q1))**2==1
  assert int(sp.jacobi_symbol(2,q2))==1
  assert int(sp.jacobi_symbol(pp,q2))==int(sp.jacobi_symbol(aa-bb,q2))**2==1
  assert pow(aa%pp,pp//2,pp)==pow((aa+bb)%pp,pp//2,pp)==1
  ii=bb*pow(aa,-1,pp)%pp
  assert ii*ii%pp==pp-1 and pow(ii,pp//4,pp)==1
  assert ((aa+bb)**2-2*aa*aa*ii)%pp==0
  assert pow(2,pp//4,pp)==1
  signed_cases.add((aa>0,bb>0));ray_cases.append((pp,aa,bb))
  if pp<2500:
   zz=next(z for z in range(pp) if pow(z,8,pp)==pp-1)
   tt=next(t for t in range(pp) if pow(t,4,pp)==2)
   assert pow(zz,8,pp)==pp-1 and pow(tt,4,pp)==2
   small_root_cases.append((pp,aa,bb,zz,tt))
assert len(ray_cases)>100 and signed_cases=={(False,False),(False,True),(True,False),(True,True)}
assert small_root_cases and any(aa<0 for _,aa,_,_,_ in small_root_cases)
# Explicit denominator-one convention stays supported in the generic Jacobi
# helpers even when this particular stronger signed ray does not attain it.
for pp in [17,97,113,257]:
 assert sp.jacobi_symbol(pp,1)==sp.jacobi_symbol(2,1)==sp.jacobi_symbol(0,1)==1
# Necessary stronger ray: p≡1 mod16 alone does not give fourth-root2.
assert 17%16==1 and not any(pow(t,4,17)==2 for t in range(17))
a,b=sp.symbols('a b')
assert sp.expand((a-b)**2-2*(a*a+b*b)+(a+b)**2)==0
for d in [1,3,5,7]:
 for k in [-5,-1,1,6]:
  assert -(d*k)**2==d*(-d*k*k)
finite=(HERE/'FiniteRayRootAlgebra318.lean').read_text()
for tok in ['ZMod.euler_criterion','4∣p/2','8∣p/2','i^(p/4)=1','(a+b)^2=2*a^2*i','t^4=2','z^8= -1']:
 assert tok in finite,tok
jac=(HERE/'SignedJacobiRay318.lean').read_text()
for tok in ['quadratic_reciprocity_one_mod_four','a.natAbs','haodd','hrec.symm.trans hJ','pow_left','χ₈_nat_eq_if_mod_eight','sq_nonneg (jacobiSym b q)']:
 assert tok in jac,tok
quadratic=(HERE/'GaussianRayQuadratic318.lean').read_text()
for tok in ['(p:ℤ)=a^2+b^2','a%16=9','b%16=0','twice_square_congruence_symbol','(a+b).natAbs','actual_roots']:
 assert tok in quadratic,tok
final=(HERE/'GaussianRayQuarterPreparation318.lean').read_text()
for tok in ['∀ i : Fin 3 × Fin 5','GaussianRayQuadratic318.actual_roots','actual_moduli_dvd_quarters','GaussianData C u w → ∀ s','quarterMinus C u w hp r','quarterPlus C u w hp r','Nat.ModEq L h h₀','(190+51*j.val)','SelectedRayEmbeddings318.ray_preparation_family','hprimary.of_dvd','hopposite.of_dvd']:
 assert tok in final,tok
assert 'SelectedQuarterOrder318.RootData' not in final.split('theorem gaussian_preparation_family',1)[1]
assert '∃ h' not in final.split('theorem gaussian_preparation_family',1)[1]
print('SIGNED_GAUSSIAN_SMALL_ROOT_DATA',small_root_cases)
print(f'PASS: {len(ray_cases)} actual signed Gaussian norm/ray prime instances in all4 sign quadrants;{len(small_root_cases)} explicit root pairs; both Jacobi denominators and q=1 convention; exact quarter Euler and norm identities; stronger-ray negative control; all15 and same-h three-pole consumer;222 exact222r1 copies')

# Exact neighboring norms, six/two valuations, signed odd factors and all
# finite CRT gcd conclusions. These checks do not assert prime existence.
norm_cases=[]
for aa in range(-247,250,16):
 for bb in range(-240,241,16):
  dm=(aa-1)**2+bb*bb;dp=(aa+1)**2+bb*bb
  A=(aa-9)//16;B=bb//16
  mm=(1+2*A)**2+4*B*B;nn=(5+8*A)**2+64*B*B
  assert dm==64*mm and dp==4*nn and mm%2==nn%2==1
  assert dm//4==16*mm>0 and dp//4==nn>0
  assert dm//4%32==16 and dp//4%2==1
  assert dm-(aa*aa+bb*bb)==1-2*aa
  assert dp-(aa*aa+bb*bb)==1+2*aa
  norm_cases.append((aa,bb,dm,dp,mm,nn))
assert len(norm_cases)>900
pair_cases=0
for x in norm_cases[::17]:
 for y in norm_cases[::19]:
  if gcd(x[2],y[3])==4:
   assert gcd(x[2]//4,y[3]//4)==1
   pair_cases+=1
continuity_cases=0
for oddL in [1,3,5,7,15,21,55,105,1155]:
 L=64*oddL
 family=[x for x in norm_cases if gcd(x[2]*x[3],oddL)==1]
 assert family
 for offset in range(0,len(family),max(1,len(family)//13)):
  selected=family[offset:offset+15]
  mm=lcm(*(x[2]//4 for x in selected));mp=lcm(*(x[3]//4 for x in selected))
  assert gcd(mm,L)==16 and gcd(mp,L)==1
  continuity_cases+=1
# Literal original two finite curve counts under the actual additional mod7
# Gaussian ray. Orientation is measured, NOT inferred as a Lean theorem.
cm_examples=[]
for aa in range(-279,282,112):
 for bb in range(-256,257,112):
  pp=aa*aa+bb*bb
  if not sp.isprime(pp) or pp>50000:continue
  assert aa%16==9 and bb%16==0 and aa%7==1 and bb%7==3
  roots2=[r for r in range(pp) if r*r%pp==2]
  assert len(roots2)==2
  counts=[]
  for rr in roots2:
   dd=(3-rr)**2%pp
   cc=1
   for xx in range(pp):
    f=(xx**3-dd*xx)%pp
    cc+=1 if f==0 else 2 if pow(f,(pp-1)//2,pp)==1 else 0
   counts.append(cc)
  dm=(aa-1)**2+bb*bb;dp=(aa+1)**2+bb*bb
  assert sorted(counts)==sorted([dm,dp])
  assert counts[0]+counts[1]==2*(pp+1)
  cm_examples.append((pp,aa,bb,roots2,counts,dm//4,dp//4))
assert len(cm_examples)>=3
# Actual source spacing with repeated positions: only distinct coefficients
# imply distinct primes, and repeated positions must use the diagonal case.
spacing_cases=0
for ww in [-31,-7,1,9,25]:
 for u0 in [10000,100000]:
  coeff=[-3,-1,0,2,2,5]
  vals=[u0+k*ww*ww for k in coeff]
  if min(vals)<=0:continue
  for i in range(len(coeff)):
   for j in range(len(coeff)):
    if coeff[i]!=coeff[j]:assert abs(vals[i]-vals[j])>=ww*ww
    else:assert vals[i]==vals[j]
    spacing_cases+=1
# Concrete CRT residue/step example with the exact shared factor16.
Pi,Mm,Mp,L,h0=1009*1013,16*13,17*19,64*3,64
assert gcd(Pi,Mp)==gcd(Pi,L)==gcd(Mm,Mp)==gcd(Mp,L)==1
assert gcd(Mm,L)==16
from sympy.ntheory.modular import solve_congruence
hh,step=solve_congruence((0,Pi**3*Mm),(1,Mp),(h0,L))
for t in [0,1,7]:
 h=int(hh+step*t)
 assert h%(Pi**3*Mm)==0 and h%Mp==1 and h%L==h0%L
assert solve_congruence((0,2),(1,2)) is None
new=(HERE/'GaussianIndexPreparation318.lean').read_text()
for tok in ['∃ T : ℚ, ∃ Q : ℕ','T≤parameter C u w → ∀ B₀','∃ h : ℕ, B₀<h ∧ 1<h','CMMatch','(190+51*j.val)','take 263','ThreeDetectorCRTWitness318.prepared_family','gaussian_preparation_family','GaussianSelectedOrders318.crt_data']:
 assert tok in new,tok
assert '∃ h' not in new.split('∃ T : ℚ',1)[0]
separation=(HERE/'GaussianPrimeSeparation318.lean').read_text()
for tok in ['k=C.coefficient i','OrderSeparation.diagonal_not_dvd','OrderSeparation.off_diagonal_not_dvd','coefficients C) Finset.univ','E<(w:ℝ)^2','Nat.coprime_of_lt_prime']:
 assert tok in separation,tok
assert separation.count('include hv in')==5
selected=(HERE/'GaussianSelectedOrders318.lean').read_text()
assert 'counts C u w hv r false i=GaussianNeighborNorms318.minus' in selected
assert 'counts C u w hv r true i=GaussianNeighborNorms318.plus' in selected
print('ACTUAL_CM_SAMPLE_DATA',cm_examples)
print(f'PASS: {len(norm_cases)} signed neighboring-norm factors;{pair_cases} gcd-four/quarter coprimality cases;{continuity_cases} exact continuity LCM gcds;{len(cm_examples)} literal original CM count examples (not a universal proof);{spacing_cases} duplicate-aware spacing cases; actual three-residue CRT and negative control; prior thresholds then produced same h/source witness;222 exact222r1 copies')

# Literal ordinate fibers, infinity, quadratic characters and all actual
# nonsquare twists over these fields, including the singular D=0 equation.
def chi(p,x):
 x%=p
 if not x:return 0
 return 1 if pow(x,(p-1)//2,p)==1 else -1
fiber_cases=twist_cases=0
for pp in list(sp.primerange(3,44)):
 counts={}
 traces={}
 for dd in range(pp):
  affine=sum((yy*yy-xx**3+dd*xx)%pp==0 for xx in range(pp) for yy in range(pp))
  tr=sum(chi(pp,xx**3-dd*xx) for xx in range(pp))
  assert affine==pp+tr
  for xx in range(pp):
   count=sum((yy*yy-xx**3+dd*xx)%pp==0 for yy in range(pp))
   assert count==1+chi(pp,xx**3-dd*xx)
   fiber_cases+=1
  counts[dd]=1+affine;traces[dd]=tr
 for dd in range(pp):
  for cc in range(1,pp):
   if chi(pp,cc)!=-1:continue
   assert traces[dd*cc*cc%pp]==-traces[dd]
   assert counts[dd]+counts[dd*cc*cc%pp]==2*(pp+1)
   twist_cases+=1
# Direct generic coordinate factorization, then original conjugate twist.
x,c,d,rho=sp.symbols('x c d rho')
assert sp.expand((c*x)**3-d*c*c*(c*x)-c**3*(x**3-d*x))==0
cc=(3+rho)/(3-rho)
assert sp.cancel((3-rho)**2*cc**2-(3+rho)**2)==0
assert sp.rem(sp.together(cc*(3-rho)**2-7).as_numer_denom()[0],rho*rho-2,rho)==0
seven_cases=[];opposite_cases=[]
for pp in list(sp.primerange(3,600)):
 if pp%4==1 and pp%7==3:
  assert chi(pp,7)==-1
  seven_cases.append(pp)
 if pp%8!=1 or pp%7!=3:continue
 roots2=[r for r in range(pp) if r*r%pp==2]
 assert len(roots2)==2
 cnt=[]
 for rr in roots2:
  dm=(3-rr)%pp;dp=(3+rr)%pp
  assert dm and dp and dm*dp%pp==7%pp
  c=dp*pow(dm,-1,pp)%pp
  assert chi(pp,c)==-1 and dm*dm*c*c%pp==dp*dp%pp
  cnt.append(pp+1+sum(chi(pp,x**3-dm*dm*x) for x in range(pp)))
 assert cnt[0]+cnt[1]==2*(pp+1)
 opposite_cases.append((pp,roots2,cnt))
# The missing mod7 hypothesis genuinely matters even under the mod16 ray.
pp=337;cnt=[]
for rr in [26,311]:cnt.append(pp+1+sum(chi(pp,x**3-(3-rr)**2*x) for x in range(pp)))
assert chi(pp,7)==1 and cnt==[356,356] and sum(cnt)!=2*(pp+1)
# All15 independent orientation choices are produced from just one count
# and the proved opposite sum; repeated positions are allowed.
orientation_cases=0
for pp,aa,bb,roots2,counts,mm,mp in cm_examples:
 dm,dp=4*mm,4*mp
 for base in [0,1]:
  count0,count1=counts[base],counts[1-base]
  assert count0 in (dm,dp) and count0+count1==dm+dp
  flip=count0!=dm
  assert (count1 if flip else count0)==dm
  assert (count0 if flip else count1)==dp
  orientation_cases+=1
choice=(HERE/'ActualCMOrientation318.lean').read_text()
for tok in ['def OneCount','counts C u w hp r false i','ActualConjugateCounts318.all_counts_sum','∃ s : Fin 3 × Fin 5 → Bool','oriented_counts']:
 assert tok in choice,tok
final=(HERE/'ConjugateIndexPreparation318.lean').read_text()
for tok in ['ActualCMOrientation318.OneCount','(∀ i, A i%7=1)','(∀ i, B i%7=3)','∃ T : ℚ, ∃ Q : ℕ','∃ s : Fin 3 × Fin 5 → Bool','∃ h : ℕ, B₀<h ∧ 1<h','take 263','(190+51*j.val)','ActualCMOrientation318.choose_orientation','GaussianIndexPreparation318.prepared_family']:
 assert tok in final,tok
assert 'CMMatch' not in final
print('ACTUAL_OPPOSITE_COUNT_DATA',opposite_cases)
print(f'PASS: {fiber_cases} literal ordinate-fiber counts;{twist_cases} actual nonsquare twists;{len(seven_cases)} mod7 reciprocity cases;{len(opposite_cases)} original conjugate count pairs;{orientation_cases} actual orientation selections; exact coordinate identities and p337 missing-mod7 negative control; same-h consumer with one remaining unordered count;222 exact222r1 copies')
