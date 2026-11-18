"""Stdlib exact construction of both actual ordinates, including two earlier first-class targets."""
from fractions import Fraction as F
from math import prod,gcd,isqrt
from hashlib import sha256
import json
def val(p,x):
    x=F(x);assert x
    def v(n):
        k=0
        while n%p==0:n//=p;k+=1
        return k
    return v(x.numerator)-v(x.denominator)
def xj(b,l):return (l*l-3*b)/(2*l),(l*l+3*b)/(2*l)
def cubic(n,x):return x*(x-n)*(x+3*n)
def check_pair(b,E,S,y,z):
    B=17*b;V=B*B*(1-b/17);assert 0<b<17 and E*S*y*z
    assert y*y==cubic(E,B) and z*z==cubic(E*V,B*S*S)
def certificate(factors):
    m=prod(factors);beta=17*m;s,J=xj(beta,F(1));sp=s*s-beta
    assert sp>0 and J*J==s*s+3*beta
    L=m*2**(7+max(0,val(2,sp)))*3**(5+max(0,val(3,sp)))*17**3
    for q in range(5,500):
        if not all(q%i for i in range(2,isqrt(q)+1)) or (102*m*sp.numerator*J.numerator)%q==0:continue
        rr=next((i for i in range(1,q) if i*i%q==beta%q),None)
        if rr is not None:break
    else:raise AssertionError()
    targ=3*rr%q
    z0=1+L*((targ-1)*pow(L,-1,q)%q)
    while True:
        t,K=xj(beta,F(z0))
        if t>0 and t*t>beta and val(q,t*t-beta)==1:break
        z0+=q*L
    h=(s-t)/(s*t-beta);c=beta*h*h;d=1-c;w=17*h;b0=m*w*w;B=17*b0
    assert d==(s*s-beta)*(t*t-beta)/(s*t-beta)**2
    es=(s*s-beta)/(s*s+3*beta);et=(t*t-beta)/(t*t+3*beta)
    T=K*(s*s-beta)/((s*t-beta)*J);assert T*T==d*es/et
    E=B*es;S=B*T
    ys=w**3*beta*(4*beta*s/(s*s+3*beta))
    yt=(w*S)**3*beta*(4*beta*t/(t*t+3*beta))
    check_pair(b0,E,S,ys,yt)
    assert val(q,d)==1 and all(val(p,h)>=0 for p in factors)
    a,b,g=(val(p,h) for p in (2,3,17));assert a>=3 and b>=2 and g>=1
    lam=F(2**(a-1)*3**(b-1)*17**g)
    X=(d*lam**2-2*d*lam-c)/(c+d*lam**2);Z=1+lam*(X-1)
    assert c*X**2+d*Z**2==1 and X*Z
    bb=b0*X**2;E1=E*X**2;S1=S*X**2*Z;y1=ys*X**3;y2=yt*X**9*Z**3
    check_pair(bb,E1,S1,y1,y2)
    assert [val(p,bb) for p in (2,3,17)]==[4,2,2] and all(val(p,bb)>=0 for p in factors)
    assert isqrt(bb.denominator)**2==bb.denominator and val(q,1-bb/17)%2==1
    assert all(v>0 for v in (es,et)) and 1-bb/17==d*Z**2
    def fmt(x):return str(x.numerator)+'/'+str(x.denominator)
    return dict(m=m,prime_factors=factors,marker=q,hyperbola_parameters=[1,z0],transport_slope=lam.numerator,
        exact_depths=[4,2,2],marker_v_final=val(q,1-bb/17),
        nonzero_witness_sha256=sha256(('\n'.join(map(fmt,(bb,E1,S1,y1,y2)))+'\n').encode()).hexdigest())
ROW=[6355619657003953590668572692660794222201617,7629921398233246285597621517513600811116698417,15253487176809488617604574462334540828011195217,21411131835217,1205147289998231249041393360084651361989395217]
if __name__=='__main__':
    import sys
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    targets=[[],[9145],[5,11,163,661,733,1489,1861],ROW]
    targets[1]=[5,31,59]
    assert 11*4376874610839020==4*prod(targets[2])
    print(json.dumps([certificate(factors) for factors in targets],indent=2))
