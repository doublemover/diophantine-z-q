"""Verify exact source constants, a literal common-index control, mod-29 Frobenius
witness, finite-prime certificate(s); no Lean, CAS, search service, or external packages."""
from fractions import Fraction as F
from pathlib import Path
import json, math
L=114444
coeff=[4376874610839020,101783690143177584,800910366213064752,2642145132961084032,3147690941013049344]
def r(a):return sum(c*(a*(a+1))**j for j,c in enumerate(coeff))
def f(a):return 1+L*r(a)
T=(L*L-11)**2-72
def chi(a,p):return {0:0,1:1,p-1:-1}[pow(a%p,(p-1)//2,p)]
def mod(a,p):return a.numerator*pow(a.denominator,-1,p)%p
def vp(a,p):
    if not a:return math.inf
    x,y=a.numerator,a.denominator;v=0
    while x%p==0:x//=p;v+=1
    while y%p==0:y//=p;v-=1
    return v
def ob(p):return all(chi(s,p)==-1 for s in [2,11,17,T])
def prime(p):return p>=2 and all(p%t for t in range(2,math.isqrt(p)+1))
def pmul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return c
def divrem(a,b,p):
    a=list(a)
    while a and not a[-1]%p:a.pop()
    while len(a)>=len(b):
        g=a[-1]*pow(b[-1],-1,p)%p; n=len(a)-len(b)
        for i,v in enumerate(b):a[n+i]=(a[n+i]-g*v)%p
        while a and not a[-1]:a.pop()
    return a
def qr(z,w=0):return F(z),F(w)
def plus(x,y):return x[0]+y[0],x[1]+y[1]
def sub(x,y):return x[0]-y[0],x[1]-y[1]
def mul(x,y):return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def norm(x):return x[0]**2-2*x[1]**2
def div(x,y):return mul(x,(y[0]/norm(y),-y[1]/norm(y)))
def sq(x):return mul(x,x)
def chart(x,y):
    delta=qr(11,-6);t=sq(x);w=plus(t,delta)
    return div(mul(qr(2),y),w),div(plus(sub(sq(t),mul(qr(6),mul(t,delta))),sq(delta)),sq(w))
def sample():
    delta=qr(11,-6);k=qr(-1,F(7,4));m=qr(F(39,8),F(-9,2))
    U,V=chart(qr(1,1),qr(0,2)); un,vn=chart(qr(1,1),qr(0,-2)) # H=1, n=-1
    assert plus(sq(V),mul(delta,sq(sq(U))))==qr(1)
    sw=div(sub(div(mul(k,vn),un),m),plus(sq(k),mul(delta,sq(un))))
    c=norm(mul(un,sw)); J=sq(U)[0];H=norm(U)
    assert F(1,100)<abs(H)<=1 and 0<=J<=1 and 0<abs(c)<1
    rr=r(0);A=L*rr;N=1+(H/rr)**2+2*J/rr;Q=c/(H*rr**15);W=N*N+rr*Q*Q
    b=A*(W/(1+A))**2;D=1-b/17;z=vp(D,29)
    assert z==vp(b,29)==-2 and chi(mod(D*29**2,29),29)==-1 and 0<b<17
    return {k:str(a) for k,a in dict(w33=J,w37=H,inverseNorm_m1=c,b=b,complement=D).items()}
def compute():
    assert L==11*102**2
    p=29;rr=r(0)%p
    assert rr==26 and ob(p) and T==171542649684398265553
    assert ((1-11*rr**2)**2-2*(6*rr**2)**2)%29==2
    roots=[a for a in range(p) if not f(a)%p];assert roots==[0,3,25,28]
    g=[11]
    for a in roots:g=pmul(g,[-a,1],p)
    quartic=[-13,9,10,2,1];g=pmul(g,quartic,p)
    assert all(sum(c*x**i for i,c in enumerate(g))%p==f(x)%p for x in range(p))
    assert not any(sum(c*x**i for i,c in enumerate(quartic))%p==0 for x in range(p))
    assert all(divrem(quartic,[i,j,1],p) for i in range(p) for j in range(p))
    assert all(c%17==0 for c in coeff[1:]) and coeff[0]%17==5
    assert F(1728*4*(-13)**3,4*(-13)**3+70**2)==F(35152,9)
    s=sample()
    hits=[]
    for q in range(3,1400,2):
        if prime(q) and ob(q):
            ar=[a for a in range(q) if f(a)%q==0]
            if ar:hits.append([q,ar])
    return {'p29_residue_factors':{'leading':11,'roots':roots,'quartic_ascending':quartic},
       'sign_test_constant':T,'prime_examples_below_1400':hits,'literal_control_a0_h1_n_minus1':s}
if __name__=='__main__':print(json.dumps(compute(),indent=2))
