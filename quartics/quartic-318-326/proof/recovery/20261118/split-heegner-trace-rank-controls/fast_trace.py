"""Exact proof obligations at level 48 + Arb eta/derivative CM trace.
Usage python fast_trace.py 23 [bits]. Failure of a denominator or interval test is inconclusive.
"""
from flint import acb,arb,ctx,fmpz
from math import isqrt,gcd,prod
from functools import cache
import sys,json,random

def reduced(d):
    out=[]
    for a in range(1,isqrt(d//3)+1):
        for b in range(-a,a+1):
            if (b*b+d)%(4*a):continue
            c=(b*b+d)//(4*a)
            if c<a or (b<0 and (a==c or a==-b)) or gcd(a,gcd(b,c))!=1:continue
            out.append((a,b,c))
    return out

def egcd(a,b):
    if b==0:return (1 if a>0 else -1,0)
    r,s=egcd(b,a%b);return s,r-(a//b)*s

def oriented(R,r):
    a,b,c=R;best=None
    for v in range(0,49):
        for u in range(-48,49):
            if gcd(u,v)!=1: continue
            A=a*u*u+b*u*v+c*v*v
            if A%48 or (best and A>=best[0]):continue
            y,nx=egcd(u,v);x=-nx
            assert u*y-v*x==1
            B=2*a*u*x+b*(u*y+v*x)+2*c*v*y
            if (B-r)%96:continue
            B=(B+A)%(2*A)-A;C=(B*B+4*a*c-b*b)//(4*A)
            assert B*B-4*A*C==b*b-4*a*c and (B-r)%96==0
            best=(A,B,C)
    if best is None:raise ValueError("no oriented matrix in search box; enlarge box")
    return best

def point_at(d,F):
    a,b,c=F;tau=acb(-b,arb(d).sqrt())/(2*a);pi2=arb.pi()**2
    @cache
    def jets(k):
        z=tau*k
        dt1=acb(0).modular_theta(z,1)[0];dt3=acb(0).modular_theta(z,3)[0]
        return z.modular_eta(),-k*dt3/(24*pi2*dt1)
    def prodjet(exps):
        y=acb(1);g=acb(0)
        for k,n in exps:
            h,j=jets(k);y*=h**n;g+=n*j
        return y,g*y
    f,df=prodjet([(2,1),(4,1),(6,1),(12,1)])
    B,dB=prodjet([(4,1),(8,1),(12,1),(24,1)])
    g,dg=prodjet([(4,4),(12,4),(2,-1),(6,-1),(8,-1),(24,-1)])
    A=(f+g)/2;dA=(df+dg)/2
    x=B/A;y=(A*dB-B*dA)/A**3
    t=x-1/x;w=y/(x*x);X=(w+t*t+2)/2;Y=t*X
    assert (Y*Y-X*(X+1)*(X-3)).contains(0) and Y.is_finite()
    return X,Y

def add(P,Q):
    x,y=P;X,Y=Q
    assert not (X-x).contains(0)
    s=(Y-y)/(X-x);v=s*s+2-x-X
    return v,s*(x-v)-y
def double(P):
    x,y=P;assert not y.contains(0)
    s=(3*x*x-4*x-3)/(2*y);v=s*s+2-2*x;return v,s*(x-v)-y

def cert(d,bits):
    ctx.prec=bits
    fac=fmpz(d).factor()
    assert d>0 and d%24==23 and prod(int(p) for p,e in fac)==d
    assert all(p.is_prime() and e==1 for p,e in fac)
    roots=[r for r in range(96) if (r*r+d)%192==0]
    r=min(roots);Z=reduced(d);H=[oriented(z,r) for z in Z]
    pts=[point_at(d,z) for z in H]
    random.Random(0).shuffle(pts)  # fixed order only; the sum is independent of ordering
    # Balanced addition controls interval propagation; a vertical/coincident branch is inconclusive.
    while len(pts)>1:
        pts=[add(pts[i],pts[i+1]) if i+1<len(pts) else pts[i] for i in range(0,len(pts),2)]
    R=pts[0];U=double(R);V=double(U)
    assert U[0].imag.contains(0) and U[1].real.contains(0)
    assert not U[1].imag.contains(0) and V[0].is_finite() and V[1].is_finite()
    return dict(d=d,orient=r,h=len(Z),bits=bits,forms=H,twice_trace=[str(w) for w in U],
        four_times_trace_is_affine=True)
if __name__=='__main__':
    print(json.dumps(cert(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 256),indent=2))
