"""Exact arithmetic controls, no CAS. Coordinates in order X,X-r1,X-r2."""
from fractions import Fraction as F
from math import prod,gcd
from itertools import product
import json
def res(x,n):
    x=F(x); return x.numerator*pow(x.denominator,-1,n)%n
def chi(x,p): return {1:1,p-1:-1}[pow(res(x,p),(p-1)//2,p)]
def hensel2(x,b,p):
    b%=p; assert (x-b*b)%p==0
    z=b+p*((x-b*b)//p*pow(2*b,-1,p)%p)
    assert (x-z*z)%(p*p)==0
    return z
def test(ps,theta,ell,a,e,k):
    beta=prod(ps); a0,a1=F(ell,e),F(a,e)
    assert ell**2-beta*a*a==theta*e**2 and gcd(ell,beta*theta)==1
    m=beta*k*k; r1=beta*theta*(1-m)*(25*m-9);r2=16*beta*theta*(1-m)*m
    A=beta*(a1*(3+5*m)+8*k*a0); B=a0*(3+5*m)+8*beta*k*a1
    assert A*A-beta*B*B==r1 and r2-r1==9*beta*theta*(1-m)**2
    vp=[]
    for p in ps:
        n=p*p
        g=hensel2(theta,-res(a0,p),p); h=hensel2(1-m,1,p)
        x1=4*beta*k*g*h; x2=3*g*(1-m)
        assert (x1*x1-beta*x2*x2-r1)%n==(x1*x1-r2)%n==0
        z=res(x2*(A*x1-beta*B*x2-r1),n);assert z%p==0 and z
        s=chi(F(z//p,beta//p),p)*chi(-1,p)
        assert s==chi(6*a0,p);vp.append(s)
    n=9
    if k%3==0:
        assert k%9 and r1//9%3==2 and r2//9%3==1 and r1%9==r2%9==0
        yy=res(F(r2-r1,9*beta),n);xx=r2//9%n
        pts=[(x,y,0) for x,y in product(range(n),repeat=2) if x*x%n==xx and y*y%n==yy and
            res((A/3)*x-beta*(B/3)*y-r1//9,3) and y%3]
        assert pts; sign3=-1;val3=3
    else:
        assert r1%3==r2%3==2 and (r1-r2)//9%3==1
        yy=res(F(1-r1,beta),n);zz=res(F(1-r2,beta),n)
        pts=[(x,y,z) for x,y,z in product([-1,1],range(n),range(n)) if y*y%n==yy and z*z%n==zz and
            res(A*x-beta*B*y-r1,3) and (y-z)%3]
        assert pts;sign3=1;val3=0
    bit=prod(chi(ell,p) for p in ps);fourth=prod(1 if pow(theta,(p-1)//4,p)==1 else -1 for p in ps)
    assert bit==fourth and prod(vp)==-bit and prod(vp)*sign3==(bit if k%3==0 else -bit)
    return dict(k=k,beta_prime_symbols=vp,chosen_3adic_residues=list(pts[0]),tangent_product_v3=val3,global_sign=prod(vp)*sign3)
examples=[([17],409,1073,12,53),([17],457,439715,12,20569),([17,409,2857,3673,6121,6529],943689409057,20491203655,12,1)]
if __name__=='__main__':
    out=[]
    for ps,t,l,a,e in examples:
        runs=[test(ps,t,l,a,e,k) for h in range(2,8) for k in (2**h,3*2**h)]
        out.append(dict(beta=prod(ps),theta=t,ell=l,a=a,e=e,slopes=runs))
    print(json.dumps(out,indent=2))
