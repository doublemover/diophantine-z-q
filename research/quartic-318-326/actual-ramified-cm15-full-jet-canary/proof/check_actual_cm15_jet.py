#!/usr/bin/env python3
"""Exact X0(32), CM discriminant -15, ramified mod-5 jet; standard library."""
from fractions import Fraction as F
from itertools import product
import json

class Bi:
    """Q[e,r], ordered 1,e,r,er, e²=5, r²=-3."""
    def __init__(self,*v): self.v=tuple(F(x) for x in v)+(F(0),)*(4-len(v))
    @staticmethod
    def cast(x): return x if isinstance(x,Bi) else Bi(x)
    def __add__(a,b): return Bi(*(x+y for x,y in zip(a.v,a.cast(b).v)))
    __radd__=__add__
    def __neg__(a): return Bi(*(-x for x in a.v))
    def __sub__(a,b): return a+-a.cast(b)
    def __rsub__(a,b): return a.cast(b)+-a
    def __mul__(a,b):
        z=[F(0)]*4
        for i,j in product(range(4),repeat=2):
            z[i^j]+=a.v[i]*a.cast(b).v[j]*(5 if i&j&1 else 1)*(-3 if i&j&2 else 1)
        return Bi(*z)
    __rmul__=__mul__
    def __pow__(a,n):
        if n<0:return a.inv()**(-n)
        if not n:return Bi(1)
        h=a**(n//2)
        return h*h*(a if n%2 else 1)
    def conj(a,mask): return Bi(*(x*(-1)**((i&mask).bit_count()) for i,x in enumerate(a.v)))
    def inv(a):
        adj=a.conj(1)*a.conj(2)*a.conj(3); n=a*adj
        assert n.v[0] and n==n.v[0]
        return Bi(*(x/n.v[0] for x in adj.v))
    def __truediv__(a,b):return a*a.cast(b).inv()
    def __rtruediv__(a,b):return a.cast(b)*a.inv()
    def __eq__(a,b):return a.v==a.cast(b).v
    def out(a):return [str(x) for x in a.v]
    def red(a):
        return [x.numerator*pow(x.denominator,-1,5)%5 for x in a.v]

eps,rho=Bi(0,1),Bi(0,0,1)
jp=(-191025+85995*eps)/2
jm=jp.conj(1)
assert jp*jp+191025*jp-121287375==0
assert jp+jm==-191025 and jp*jm==-121287375
both=[]
for sign in (1,-1):
    u=(-49-21*eps+sign*rho*(495+231*eps))/4
    v=u.conj(3)
    reverse=4096/u
    assert v!=reverse
    assert (u+256)**3==jp*u**2 and (u+16)**3==jm*u
    assert (v+256)**3==jm*v**2 and (v+16)**3==jp*v
    assert 4096/((-49-21*eps-sign*rho*(495+231*eps))/4)==v
    # The third source root is not a horizontal arrow to jm.
    nonhorizontal=43008*eps-96256
    assert (nonhorizontal+256)**3==jp*nonhorizontal**2
    assert (nonhorizontal+16)**3!=jm*nonhorizontal
    current=[u,v,u,v,u]
    towers={2:[u.out(),v.out()]}
    for n,h,k in ((4,16,16),(8,4,8),(16,2,4)):
        following=[(B-h*A)/(A+k) for A,B in zip(current,current[1:])]
        for A,B,C in zip(current,current[1:],following):
            assert C*C==A*(C+h) and B==C*(C+k)
        current=following
        towers[n]=[z.out() for z in current[:2]]
    X=current[1]+2
    Y=(1+sign*eps*rho)/2
    assert (X,Y)==((-1+eps-sign*(3+eps)*rho)/4,Y)
    assert Y*Y==X**3+4*X
    Xb=X.conj(3)
    assert Xb!=X and Y.conj(3)==Y
    m=-2*Y/(Xb-X); U=m*m-X-Xb; V=m*(X-U)-Y
    assert (U,V)==(1,eps) and V*V==U**3+4*U
    Q=((U+4/U)/4,V*(1-4/(U*U))/8)
    assert Q==(F(5,4),-3*eps/8) and Q[1]**2==Q[0]**3-Q[0]
    both.append(dict(orientation=sign,ordered_tower=towers,X=X.out(),Y=Y.out(),
                     diff_X0_32=[U.out(),V.out()],trace_on_E=[q.out() for q in Q]))

# Prove corrected tower identities by Laurent q-exp plus degree-two bounds.
N=9
def mul(a,b):
    return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(N+1)]
def power_factor(m,n):
    a=[1]+[0]*N
    for j in range(1,N//m+1):
        a[m*j]=-a[m*(j-1)]*F(n-j+1,j)
    return a
ts={2:{1:24,2:-24},4:{1:8,4:-8},
    8:{1:4,4:2,2:-2,8:-4},16:{1:2,8:1,2:-1,16:-2}}
series={}
for lev,eta in ts.items():
    c=[1]+[0]*N
    for d,weight in eta.items():
        for m in range(d,N+1,d):c=mul(c,power_factor(m,weight))
    assert all(F(a).denominator==1 for a in c)
    series[lev]=[int(a) for a in c]
for lev,h,k in ((2,16,16),(4,4,8),(8,2,4)):
    a,b=series[lev],series[2*lev]
    bh=b.copy();bh[1]+=h
    bk=b.copy();bk[1]+=k
    assert mul(a,bh)==mul(b,b)
    assert [a[i//2] if i%2==0 else 0 for i in range(N+1)]==mul(b,bk)

# True F25[eps]/eps² check using the reductions of the integral biquadratic basis.
def EQ(x,y):return Bi.cast(x).red()==Bi.cast(y).red()
A=eps*(1-rho); R=-1+eps*(1-rho)/3
t2_deriv=Bi(*both[0]['ordered_tower'][2][0]).v
assert EQ(eps*(t2_deriv[1]+t2_deriv[3]*rho),A)
assert EQ(R**3+A*R+1,0)
b1=3*R*R+A
v=3*rho + eps*(1+2*rho)  # order-four kernel, x(P4)-x(R)
assert EQ(v*v,b1)
t4=Bi(*both[0]['ordered_tower'][4][0]); t40=t4.v[0]+t4.v[2]*rho
assert EQ(t40*(3*R.conj(1).v[0]-2*(3*rho)),64*(3*rho))
R2=R+2*v; A1=A-5*b1; B1=1-7*R*b1
assert EQ(R2**3+A1*R2+B1,0)
b2=3*R2*R2+A1; A2=A1-5*b2; B2=B1-7*R2*b2
scale=(1-eps*rho)/2
assert EQ(A2,scale**4*A) and EQ(B2,scale**6)
assert not EQ(B2,((1+eps*rho)/2)**6)
# O(eps^0): alpha=1-2Omega, hence the negative coefficient of 2(b1+b2).
coeffs=(-2*(b1+b2)).red()
c=Bi(coeffs[0],0,coeffs[2])
assert EQ(c,1+2*rho)
assert EQ(c*rho/(-3),2*(1-rho)) # matches Hasse coefficient in y²=x³+eps(1-rho)x+1

# Independent actual modular differential evaluation versus rational group law.
u1=(1-rho)/4
u2=(-1-rho)/4
J=4*2*(u1-u2)
assert EQ(J,4)
P=(F(25,4),F(-75,8))
for _ in range(2):
    x,y=P; m=(3*x*x-25)/(2*y); xnew=m*m-2*x
    P=(xnew,m*(x-xnew)-y)
    assert P[1]**2==P[0]**3-25*P[0]
x,y=P
assert EQ(-x/y,J)
good_counts={p:1+sum((yy*yy-xx**3+25*xx)%p==0 for xx,yy in product(range(p),repeat=2)) for p in (3,7)}
assert good_counts=={3:4,7:8}
print(json.dumps(dict(basis='1,e,r,er; e²=5,r²=-3',oriented_CM=both,
                      eta_tower_q_coefficients=series,scale_F25_dual=scale.red(),
                      oriented_alpha_first_coefficient=c.red(),
                      Hasse_over_epsilon=(2*(1-rho)).red(),
                      modular_evaluations_F25=[u1.red(),u2.red()],
                      four_times_twist=[str(x),str(y)],twist_good_counts=good_counts,jet_mod5=J.red()[0]),indent=2))
