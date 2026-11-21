"""Exact denominator parity at primes dividing 1+A, not the whole denominator."""
import contextlib,io,math,sys,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'rc-linked-scalar-specialization-r1'))
with contextlib.redirect_stdout(io.StringIO()): import check_actual_scalar_modular as F
from sympy import sqrt_mod,isprime
C=F.C; eta=-2*1861*2027*83761

def corn(p):
    r=int(sqrt_mod(-1,p))
    for a in (r,p-r):
        x=p
        while a*a>p:x,a=a,x%a
        b=math.isqrt(p-a*a)
        if a*a+b*b==p:return a if a%2 else b
    raise ValueError('no validated Gaussian coordinate')
def cls(x,p):return 1 if pow(x%p,(p-1)//2,p)==1 else -1
R=[]
ps=(29,181,1346909,70850399941)
assert math.prod(ps)==1+C.A
for p in ps:
    assert isprime(p) and cls(2,p)==-1
    a=corn(p); trace0=4*a*a-2*p
    o=p*p+1-cls(7,p)*trace0
    e=C.E(p)
    assert e.nsmul(o) is None
    u=F.chartmod(e,C.h%o)
    v=F.chartmod(e,C.shift%o)
    H=F.parent_poly(p,[u]);I=F.parent_poly(p,[v]);f=(u[0]**2+2*u[1]**2)%p
    if H:
        Q=I*pow(H*pow(C.R,15,p),-1,p)%p
        N=(1+(H*pow(C.R,-1,p)%p)**2+2*f*pow(C.R,-1,p))%p
        W=(N*N+C.R*Q*Q)%p
        case='unit' if W else 'needs_refinement'
    else:
        W=None
        case='pole_even' if I else 'needs_refinement'
    R.append(dict(p=p,annihilator=o,chart_h=u,chart_i=v,H=H,I=I,W=W,case=case,eta=cls(eta,p)))
print(json.dumps(R,indent=2))
