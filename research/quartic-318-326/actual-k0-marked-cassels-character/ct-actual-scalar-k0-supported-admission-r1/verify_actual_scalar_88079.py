#!/usr/bin/env python3
"""Standalone exact arithmetic replay for one literal source place and the ten-support matrix."""
import json
from math import isqrt, prod
from pathlib import Path

HERE=Path(__file__).resolve().parent
S=json.loads((HERE/'PINNED-SCALAR-INDEX.json').read_text())
h,J,R,ex=[S[k] for k in ('h','J','R_input','N')]
assert h==473592745039516333133760
shift=6**15*3**ex*J
As=114444*R
ps=[5,11,17,163,661,733,1489,1861]
theta=[131,6551]
beta=prod(ps)
assert As==17*12**2*beta
def prime(p):
    return p>=2 and all(p%q for q in range(2,isqrt(p)+1))
assert all(prime(q) for q in ps+theta)
def leg(a,p):
    r=pow(a%p,(p-1)//2,p)
    assert r in (0,1,p-1)
    return -1 if r==p-1 else r
def tuples(xs):
    for m in range(1<<len(xs)):
        yield m,prod(p for i,p in enumerate(xs) if m>>i&1)
def kernel(xs,g):
    return [(m,d) for m,d in tuples(xs) if all(
        leg(d//(p if d%p==0 else 1),p)==leg(g*(beta//p),p)**(d%p==0) for p in ps)]
k1=kernel(ps,3)
k2=kernel(ps+theta,-3)
ks=[(m,d) for m,d in k2 if d%8 in (1,5) and leg(d,3)==1]
assert k1==[(0,1)]
assert k2==[(0,1),(156,3408665291),(850,9291112901939),(974,72485172522267769)]
assert ks==[(0,1),(974,72485172522267769)]
d=ks[-1][1]

p=88079
assert prime(p) and p%8==7 and R*(1+As)*beta*d%p!=0
s=pow(2,(p+1)//4,p)
assert s*s%p==2
roots=sorted((s,p-s))
assert roots[0]!=roots[1]
def finite_arm(s,order):
    E=(3-s)**2%p
    Q=((1+s)%p,2*s%p)
    assert (Q[1]**2-Q[0]**3+E*Q[0])%p==0
    def add(U,V):
        if U is None:return V
        if V is None:return U
        x,y=U;a,b=V
        if x==a and (y+b)%p==0:return None
        m=(3*x*x-E)*pow(2*y,-1,p)%p if x==a else (y-b)*pow(x-a,-1,p)%p
        xx=(m*m-x-a)%p
        yy=(m*(x-xx)-y)%p
        assert (yy*yy-xx**3+E*xx)%p==0
        return xx,yy
    def nsmul(n):
        U=None
        L=Q
        while n:
            if n&1:U=add(U,L)
            L=add(L,L)
            n//=2
        return U
    assert nsmul(order) is None
    assert all(nsmul(order//q) is not None for q in range(2,order+1) if order%q==0 and prime(q))
    def get_chart(i):
        Z=nsmul(i%order)
        if Z is None:return 0
        x,y=Z
        return 2*y*pow(x*x+E,-1,p)%p
    return dict(root=s,order=order,h_mod_order=h%order,shift_mod_order=shift%order,
                U_h=get_chart(h),U_shift=get_chart(shift))
arms=[finite_arm(s,o) for s,o in zip(roots,[3670,5505])]
Uh=[a['U_h'] for a in arms]
Ui=[a['U_shift'] for a in arms]
assert Uh==[16807,79510] and Ui==[17819,19933]
H=prod(Uh)%p; I=prod(Ui)%p
f=sum(u*u for u in Uh)*pow(2,-1,p)%p
Q=I*pow(H*R**15,-1,p)%p
N=(1+(H*pow(R,-1,p))**2+2*f*pow(R,-1,p))%p
W=(N*N+R*Q*Q)%p
assert (H,I,f,N,Q,W)==(78061,51599,31925,71812,13600,0)
assert leg(-3*beta,p)==1 and leg(d,p)==-1
print(json.dumps(dict(scope='same original a=0 scalar h,J; supported Sel2 restriction only',
  beta=beta,beta_primes=ps,visible_theta=theta,first_masks=k1,second_masks=k2,
  after_dyadic_ternary=ks,h=h,J=J,p=p,arms=arms,H=H,I=I,f=f,N=N,Q=Q,W=W,
  R_mod_p=R%p,normalizer_mod_p=(1+As)%p,separate_sign=leg(-3*beta,p),
  candidate_sign=leg(d,p),after_moving_place=[1]),indent=2,sort_keys=True))
