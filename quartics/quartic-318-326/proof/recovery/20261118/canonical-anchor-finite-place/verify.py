"""Standard library, exact local class / anchor checks. No floating-point decisions."""
from fractions import Fraction as F
from math import prod,isqrt,gcd
import json
def qres(x,p):
    x=F(x);return x.numerator*pow(x.denominator,-1,p)%p
def val(x,p):
    x=F(x);assert x
    a,b=abs(x.numerator),x.denominator;v=0
    while a%p==0:v+=1;a//=p
    while b%p==0:v-=1;b//=p
    return v
def prime(p):return p>1 and all(p%i for i in range(2,isqrt(p)+1))
def sq(x):
    x=F(x);return x>=0 and isqrt(x.numerator)**2==x.numerator and isqrt(x.denominator)**2==x.denominator
def chr(x,p):return pow(qres(x,p),(p-1)//2,p)
def chiunit(x,p):
    v=val(x,p);return chr(x/F(p)**v,p)
def congr(a,m,b,n):
    return a+m*((b-a)*pow(m,-1,n)%n),m*n
def constraint(c,D,p):
    e=val(D,p)%2
    cu=qres(c,p); unit=qres(D/F(p)**val(D,p),p)
    if pow(cu,(p-1)//2,p)==1:
        v=1 if e else 2
        k=p**(v+1)
        B=qres(c,k)+p**v*(unit*pow(-8*cu,-1,p)%p)
        r=next(t for t in range(p) if (t*t-B)%p==0)
        for a in range(1,v+1):
            r+=p**a*((B-r*r)//(p**a)*pow(2*r,-1,p)%p)
        assert (r*r-B)%k==0
        return r,k
    assert e==0
    r=next(t for t in range(p) if chr((t*t-c)*(t*t-9*c),p)==chr(unit,p))
    return r,p
def main():
    small=0
    for p in range(5,230):
        if not prime(p):continue
        for c in range(1,p):
            for goal in (1,next(t for t in range(2,p) if chr(t,p)==p-1)):
                r,k=constraint(F(c),F(goal),p)
                f=(r*r-c)*(r*r-9*c)
                assert val(f,p)%2==0 and chiunit(f,p)==chr(goal,p)
                small+=1
    # Direct canonical anchor and split-1 forward/back conversion at a known seed.
    m=9145;beta=17*m;t0=F(48,691);s0=F(14,691);z=17*t0*s0
    b0=m*z*z; u=2-51*t0*t0; c=F(m,17); d=1-b0/17
    theta=29*12413*438313
    assert all(prime(p) for p in (29,12413,438313))
    e=F(1,691**2);assert theta*e*e==d
    s,t,w=u,z/17,4*theta*e
    assert w*w==theta*(s*s-beta*t*t)*(s*s+3*beta*t*t)
    r=(2+u)/z; h=1/(17*r); d1=(1-c/r**2)*(1-9*c/r**2)/(1+3*c/r**2)**2
    assert d1==d and sq(theta*(1-beta*h*h)*(1-9*beta*h*h))
    # Historical target. Includes all its bad primes, not just selected places.
    ms=[409,2857,3673,6121,6529];ts=[131,577,1367,9133]
    m=prod(ms); H=20491203655; target=m*F(204,H)**2;D=1-target/17;c=F(m,17)
    assert D==F(prod(ts),H*H)
    good=sorted(set(ts+[5,7,11,13,19,23,31,41,73]))
    r,mod=8,16
    for a,n in [(9,27),(1,17)]+[(1,p) for p in ms]+[constraint(c,D,p) for p in good]:
        r,mod=congr(r,mod,a,n)
    q=next(q for q in range(5,700) if prime(q) and gcd(q,102*m*D.numerator*D.denominator*mod)==1 and chr(c,q)==1)
    a,n=constraint(c,F(q),q);r,mod=congr(r,mod,a,n)
    r+=mod*(1+isqrt(9*m))
    z=4*r/(r*r+3*c);d=(r*r-c)*(r*r-9*c)/(r*r+3*c)**2
    assert d==1-c*z*z and d>0
    for p in good+ms+[3,17]:
        x=d/D; assert val(x,p)%2==0 and chiunit(x,p)==1
    assert qres(d/D,8)==1 and val(d/D,q)%2==1
    print(json.dumps(dict(status="EXACT_FINITE_REPLAY",small_unramified_local_tests=small,
      canonical_anchor_theta=theta,older_obstructed_target=dict(m=m,theta=prod(ts),D=str(D),all_m_primes=ms,
      other_odd_test_primes=good,forced_global_difference_prime=q,seed_r=str(r),
      seed_d_numerator_digits=len(str(d.numerator)))),indent=2))
if __name__=='__main__':main()
