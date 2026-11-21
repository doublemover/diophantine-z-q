"""Exact rational norm seeds and all sixteen actual formal selector signatures."""
from fractions import Fraction as F
from math import gcd,isqrt,prod
from pathlib import Path

u,w=368900221027188880,362538667625927811
beta=199477972060937362209233596181078921
br=3110779382579465849645476448239049522505521
R=66540735456245258815946020283188225080332
k=1+2448*br
assert beta==w*w+2*(u//2)**2 and u%2==0 and br==(11*359)**2*beta==187*R//4
assert R==4*((3723*1235**2-2401)//2)*((3723*1235**2-1)//2)*(7446*1235**2-1)*(119136*1235**2+343)
z=F(u,w); t0=F(1,3*w); M=z*z+2; lam=M/18
assert lam==beta*t0*t0
Q2=z*z-40*z-32; C3=7*z**3+16*z*z+32*z+32
e=-8*z*z*(z+4)*M*C3/9
f=-2*z*z*(z-4)*(z+4)*M*Q2/9
assert f-e==6*z**4*(z+4)**2*M
X=-4*z*(z-2)*M/3; Be=12*z*(z*z+2*z+4); Bf=6*z*(z*z-4*z-8)
assert X*X-lam*Be*Be==e and X*X-lam*Bf*Bf==f

def mod(x,m):
    if not isinstance(x,F):return x%m
    return x.numerator * pow(x.denominator,-1,m) % m

def vp(x,p):
    x=F(x); a,b=x.numerator,x.denominator
    d=0
    while a%p==0:a//=p;d+=1
    while b%p==0:b//=p;d-=1
    return d

def chars(r,m):
    a=mod(X,m); b=mod(e,m); d=mod(e-f,m); h=mod(Be,m); t=mod(Bf,m)
    return tuple(val%m for val in ((a+r*t)*b*d*pow(r,-1,m),(a-r*t)*b*d*pow(-r,-1,m),
           (a-r*h)*d*pow(r,-1,m),(a+r*h)*d*pow(-r,-1,m)))

def checkprime(p):
    assert p>1 and all(p%d for d in range(2,isqrt(p)+1))

for p,rankpair,us in ((13,(0,1),(7,12,10,10)),(37649,(1,0),(20823,22838,36309,12888))):
    checkprime(p)
    assert (vp(e,p),vp(f,p))==rankpair and vp(e-f,p)==vp(lam,p)==0
    assert (R%p,br%p,k%p,(k*k-144*br)%p)==us
    rr=next(r for r in range(1,p) if r*r%p==mod(lam,p))
    rp=next(rr+l*p for l in range(p) if (rr+l*p)**2%(p*p)==mod(lam,p*p))
    bits=tuple(int(x%p==0) for x in chars(rp,p*p))
    assert bits in ((1,0,0,0),(0,1,0,0)) if p==13 else bits in ((1,1,0,1),(1,1,1,0))
    assert all(x%(p*p) for x in chars(rp,p*p))
assert (mod(e/17,17),mod(f/17,17))==(1,8)
assert pow(-7,8,17)==pow(56,8,17)==16

p2guard=[]
expected=Path(__file__).with_name('EXACT-SOURCE-CONTROLS.txt')
for ln in expected.read_text().splitlines():
    p,s,r,m,A,ce,ceb,cf,cfb,mm,W=map(int,ln.split()[:-1]); signs=ln.split()[-1]
    checkprime(p)
    assert p>64 and gcd(p,2*3*R*br*k*(k*k-144*br))==1
    assert vp(e,p)==vp(f,p)==vp(e-f,p)==vp(lam,p)==0
    assert s*s%p==beta%p and r==mod(t0*s,p)
    assert pow(m,4,p)==A and m>0 and m<p
    assert A==pow(R,29,p)*(k*pow(12*11*359*s,-1,p)-1)%p
    assert chars(r,p)==(ce,ceb,cf,cfb)
    assert mod(12*(1+pow(m,4,p)*pow(R,-29,p))*pow(k,-1,p)*11*359*s,p)==1
    assert mm%p==m and 0<mm<p*p
    q=p*p; assert W==(1+pow(mm,4,q)*pow(R,-29,q))%q
    assert (1-br*pow(12*W*pow(k,-1,q),2,q))%q==p
    assert ''.join('+' if pow(c,(p-1)//2,p)==1 else '-' for c in chars(r,p))==signs
    assert all(chars(r,p))
    p2guard.append((p,signs))
assert len(p2guard)==16 and len(set(p for p,s in p2guard))==len(set(s for p,s in p2guard))==16
print('PASS: exact tangent norms, fixed valuation independence and 16 source p² stencils')
