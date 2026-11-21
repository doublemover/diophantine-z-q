"""Standalone constant-level-15 positive and Hasse-failure Ready controls."""
from fractions import Fraction as F
from math import factorial, gcd, isqrt
import hashlib, json

Q=10**30
N=100_000
beta=17

def ls(k,p):
    a=pow(k%p,(p-1)//2,p)
    return -1 if a==p-1 else a
def vp(n,p):
    assert n
    k=0
    while n%p==0:
        n//=p; k+=1
    return k
def ready(theta,numer,denom):
    c=F(numer,denom)
    e=F(1,denom)
    b=(17*c)**2
    assert beta*c*c+theta*e*e==1
    assert 0<b<17 and isqrt(b.denominator)**2==b.denominator
    v=[vp(b.numerator,p)-vp(b.denominator,p) for p in (2,3,17)]
    assert v[0]>=3 and v[1]>=1 and v[2]>=2
    assert all(theta%p for p in range(2,isqrt(theta)+1))
    assert theta%24==1 and ls(theta,17)==1 and ls(17,theta)==1
    assert ls(theta,5)==1 and ls(beta,5)==-1
    assert ls(3,17)==ls(5,17)==-1 and theta%4==1
    # Finite place consequences used for both exact two-dimensional caps.
    assert [ls(x,3) for x in (-1,beta,theta)]==[-1,-1,1]
    d=beta*theta
    assert d%24==17 and gcd(d,15)==1
    assert ls(d,3)*ls(d,5)==1
    return b,c,e,v,d

def val(x,p): return vp(x.numerator,p)-vp(x.denominator,p)
def unit(x,p):
    v=val(x,p)
    z=x*F(p)**(-v)
    return z.numerator*pow(z.denominator,-1,p)%p
def retune(theta,C,D):
    # Slope m from the rational point (C/D,1/D) on 17c²+theta e²=1.
    for j in range(1,29*29):
        m=16*27*17*j
        den=17+theta*m*m
        if vp(den,29)!=1: continue
        c=F(C*(theta*m*m-17)-2*theta*m,D*den)
        e=F(17-theta*m*m-34*m*C,D*den)
        if val(c,17)!=0: continue
        assert 17*c*c+theta*e*e==1
        assert [val(c,p) for p in (2,3)]==[vp(C,p) for p in (2,3)]
        assert val(c,29)==-1
        b=(17*c)**2
        assert 0<b<17 and isqrt(b.denominator)**2==b.denominator
        delta=theta*e*e
        shortcut=25-9*17*c*c
        assert val(delta,29)==val(shortcut,29)==-2
        assert ls(unit(delta,29),29)==ls(unit(shortcut,29),29)==-1
        assert ls(theta,29)==ls(17,29)==-1 and ls(17*theta,29)==1
        return c,e,dict(slope=m,c=str(c),e=str(e),b=str(b),v29_c=-1,
                        v29_stripped_delta=[-2,unit(delta,29)],
                        v29_stripped_shortcut=[-2,unit(shortcut,29)])
    raise AssertionError("retune not found")

u,W=81,117792
assert (u*u-beta,u*u-81*beta)==(16*409,72**2)
assert W**2==409*(u*u-beta)*(u*u-81*beta)
x,y=409*u*u,409*u*W
assert y*y==x*(x-17*409)*(x-81*17*409)
def raw_pair(c,e):
    b=(17*c)**2
    t=F(1,u)
    V=e*F(W,u*u)
    delta=1-beta*c*c
    G=lambda z: 1-beta*z*z
    H=lambda z: 1-9*beta*z*z
    J=lambda z: 1-81*beta*z*z
    D=lambda z: beta*G(z)*H(z)
    Av=lambda z: 1+3*beta*z*z
    Y=lambda z: beta*Av(z)*(4*beta*z)*2*(1-3*beta*z*z)
    assert V**2==delta*G(t)*J(t)
    h=V/(delta*G(t))
    assert D(3*t)==delta*D(t)*h*h and D(t)>0 and D(3*t)>0
    B=17*b
    L0,L1=17*c/Av(t),17*c*h/Av(3*t)
    T=D(t)*L0**2
    s=B*L0/L1
    y1=Y(t)*L0**3
    y2=Y(3*t)*(B*L0/h)**3
    TV=T*B*B*delta
    assert B and s and y1 and y2
    assert y1*y1==B*(B-T)*(B+3*T)
    assert y2*y2==B*s*s*(B*s*s-TV)*(B*s*s+3*TV)
    return {k:str(z) for k,z in dict(T=T,s=s,y1=y1,y2=y2).items()}

b,c,e,v,d=ready(409,24,101)
p29c,p29e,p29pos=retune(409,24,101)
p29pos["raw_PointPair"]=raw_pair(p29c,p29e)
qx,qy=-134657,11111472
assert qx==-beta*89**2 and qy*qy==qx*(qx+16*d)*(qx+25*d)
pos=dict(dual_point=[qx,qy],rank=2,isogeny_Selmer_dims=[2,2],theta=409,d=d,b=str(b),valuations=v,point=[x,y],quartic=[u,W],
         raw_PointPair=raw_pair(c,e),matched_p29=p29pos)

b,c,e,v,d=ready(769,36,151)
_,_,p29neg=retune(769,36,151)
# Eta product in increasing q degree, with the leading q^1 removed.
coeff=[1]+[0]*(N-1)
for m in (1,3,5,15):
    nxt=coeff.copy()
    for j in range(1,N):
        lo=m*j*(3*j-1)//2
        if lo>=N: break
        hi=lo+m*j
        sgn=1 if j%2==0 else -1
        for off in (lo,hi):
            for k in range(N-off):
                nxt[k+off]+=sgn*coeff[k]
    coeff=nxt
assert coeff[:17]==[1,-1,-1,-1,1,1,0,3,1,-1,-4,1,-2,0,-1,-1,2]
for n,a in enumerate(coeff,1): assert abs(a)<=2*n
cs=','.join(map(str,coeff)).encode()

def atan_bounds(k):
    z=sum((F((-1)**j,(2*j+1)*k**(2*j+1)) for j in range(30)),F(0))
    return z,z+F(1,61*k**61)
p1,p2=atan_bounds(5)
p3,p4=atan_bounds(239)
pl,ph=16*p1-4*p4,16*p2-4*p3
sl=F(isqrt(15*Q*Q),Q)
sh=sl+F(1,Q)
assert sl**2<15<sh**2
cl,ch=2*pl/(d*sh),2*ph/(d*sl)
assert 0<cl<ch<1
def exp_bounds_neg(x):
    s=sum(((-x)**i/factorial(i) for i in range(13)),F(0))
    return s-x**13/factorial(13),s
ql=exp_bounds_neg(ch)[0]
qh=exp_bounds_neg(cl)[1]
down=lambda x: x//1
up=lambda x: -(-x//1)
lq,hq=down(ql*Q),up(qh*Q)
assert 0<lq<hq<Q
lo=hi=Q
Tlo=Thi=0
weights=[[ls(j,p) for j in range(p)] for p in (17,769)]
for n,an in enumerate(coeff,1):
    lo=lo*lq//Q
    hi=-(-hi*hq//Q)
    a=2*an*weights[0][n%17]*weights[1][n%769]
    lead,tail=(lo,hi) if a>=0 else (hi,lo)
    Tlo+= a*lead//n
    Thi+=-(-a*tail//n)
remainder=F(4*hi*hq,Q*(Q-hq))
val_lo,val_hi=F(Tlo,Q)-remainder,F(Thi,Q)+remainder
assert F(3,5)<val_lo<=val_hi<1
milli=lambda l,h:[down(l*1000),up(h*1000)]
neg=dict(theta=769,d=d,b=str(b),valuations=v,root_number=1,rank=0,isogeny_Selmer_dims=[2,2],
         matched_p29=p29neg,coefficient_count=N,coefficient_sha256=hashlib.sha256(cs).hexdigest(),
         analytic_conductor=15*d*d,
         partial_sum_intervals_milli=milli(F(Tlo,Q),F(Thi,Q)),
         certified_central_value_intervals_milli=milli(val_lo,val_hi),
         remainder_upper_milli=up(remainder*1000),torsion_only_xclasses=[1,d])
print(json.dumps(dict(beta=beta,positive=pos,negative=neg,
 scope="Two standalone exact numerical Ready poles; no origin in the literal linked scalar or detector family."),
 indent=2,sort_keys=True))
