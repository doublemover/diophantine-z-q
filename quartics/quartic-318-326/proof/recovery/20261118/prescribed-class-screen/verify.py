"""Exact finite sanity checks for prescribed class / complement markers."""
from fractions import Fraction as F
from math import gcd, isqrt, prod
import json
A=[4376874610839020,101783690143177584,800910366213064752,2642145132961084032,3147690941013049344]
def crt(a,m,b,n):
    assert gcd(m,n)==1
    return a+m*((b-a)*pow(m,-1,n)%n),m*n
def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def vq(r,p):
    def z(n):
        k=0
        while n%p==0:n//=p;k+=1
        return k
    assert r
    return z(r.numerator)-z(r.denominator)
def check(m,ps,qs):
    assert prod(ps)==m and len(set(ps))==len(ps) and all(map(prime,ps))
    assert m%8==m%3==1 and pow(m,8,17)==1
    c=F(m,17);r,mod=8,16
    for b,n in [(9,27),(1,17)]+[(1,p) for p in ps]:r,mod=crt(r,mod,b,n)
    for q in qs:
        assert prime(q) and gcd(q,102*m)==1
        nd=c.numerator*pow(c.denominator,-1,q*q)%(q*q)
        a=next(j for j in range(q) if j*j%q==nd%q)
        if a*a%(q*q)==nd:a+=q
        r,mod=crt(r,mod,a,q*q)
    r+=mod*(1+isqrt(9*m))
    z=4*r/(r*r+3*c);u=2*(r*r-3*c)/(r*r+3*c)
    b0=m*z*z;C=b0/17;d=1-C;B0=17*b0
    assert 4-3*C==u*u and d==(r*r-c)*(r*r-9*c)/(r*r+3*c)**2 and 0<b0<17
    assert [vq(b0,p) for p in (2,3,17)]==[10,2,2] and all(vq(d,q)==1 for q in qs)
    slope=16;X=(d*slope*slope-2*d*slope-C)/(C+d*slope*slope)
    Z=1+slope*(X-1)
    b=b0*X*X;B=17*b;V=B*B*(1-b/17);E=B0*X*X;S=B0*X*X*Z
    y=B0**4*b0*u*X**9*Z**3
    assert E==B and (B*S*S)*(B*S*S-E*V)*(B*S*S+3*E*V)==y*y and S and y
    assert 0<b<17 and [vq(b,p) for p in (2,3,17)]==[4,2,2]
    assert isqrt(b.denominator)**2==b.denominator and b==m*(z*X)**2 and 1-b/17==d*Z**2
    assert all(vq(1-b/17,q)%2 for q in qs)
    return dict(m=m,marker_primes=qs,seed_r=str(r),slope="16",pole=str(b),
                depths=[4,2,2],first_ordinate_zero=True,second_ordinate_nonzero=True)
def main():
    assert [i%73 for i in A]==[43,0,0,0,0]
    assert (11*43)%73==35==20**2%73 and 9145%73==20 and pow(20,36,73)==72
    assert 4*12036405179807305==11*A[0]
    cases=[]
    for ps in [[],[5,31,59],[5,11,163,661,733,1489,1861]]:
        m=prod(ps)
        qs=[q for q in range(5,240) if prime(q) and gcd(q,102*m)==1 and pow(m*17,(q-1)//2,q)==1][:3]
        cases.append(check(m,ps,qs))
    print(json.dumps(dict(status="EXACT_FINITE_REPLAY",cases=cases,
      scalar_input_zero_class=12036405179807305,scalar_character_mod73=1,
      previous_family_character_mod73=-1),indent=2))
if __name__=='__main__':main()
