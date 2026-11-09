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
assert len(m['unchanged_sources'])==197 and not m['new_sources']
assert set(m['repaired_sources'])=={'LocalDerivativeSeparation318'}
for name,binding in m['unchanged_sources'].items():
    assert hashlib.sha256((HERE/(name+'.lean')).read_bytes()).hexdigest()==binding['source_sha256']
print('PASS: six actual elliptic/chart certificates, all rational source literals, depths1/1/4/4 at17, two exact second-order errors, Hensel residue6, signed product moduli, all146 coordinates/28 gates,197 exact198r1 copies and one derivative proof-only repair')

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
print('PASS: exact oriented translated ordinate modulo both original curve equations; primary z-ratio and original common G denominator; all six literal comparison/beta/Lucas polynomials; mixed8/16 and primary16 rates; quotient cancellation; order-only all15 interface and same stored poles; 197 exact198r1 copies')
