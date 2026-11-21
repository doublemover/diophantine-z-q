#!/usr/bin/env python3
"""Tiny target-coordinate calibration, no actual modular CM image as input."""
import json
from itertools import product
from math import comb, prod
p=13
def count(p,A,B,C=0):
    return 1+sum(1 if (v:=(x**3+C*x*x+A*x+B)%p)==0 else (2 if pow(v,(p-1)//2,p)==1 else 0)
                 for x in range(p))

def V(A,B,u,v):
    assert (v*v-u**3-A*u-B)%p==0 and v%p
    s=(3*u*u+A)*pow(2*v,-1,p)%p
    assert (s*s-3*u)%p==0  # 2P=-P
    return ((A-10*(3*u*u+A))%p,(B-14*(5*u**3+3*A*u+2*B))%p)

def ev(f,x):return sum(a*x**i for i,a in enumerate(f))%p

def main():
    Np=(2,3,5,7,11,37,2399)
    mu=prod(l+1 for l in Np)
    r=976393;h=-2207
    assert (r%p,h%p,pow(r%p,6,p),pow(h%p,6,p))==(2,3,12,1)
    A0=5;B0=7
    assert (76768-407-3*4)%p==0
    for x in range(p):
        assert (x*(x+76768)*(x-407)-((x+4)**3+5*(x+4)+7))%p==0
    assert count(p,A0,B0)==16
    assert count(61,-76768*407,0,76768-407)==68
    assert count(p,4,7)==14  # SS source representative, not elliptic target
    # Complete Hasse-Legendre roots and j values in F_p[sqrt 2], using p^2 order.
    def a2(x,y):return ((x[0]+y[0])%p,(x[1]+y[1])%p)
    def m2(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    def pw2(x,n):
        t=(1,0)
        while n:
            if n&1:t=m2(t,x)
            x=m2(x,x);n//=2
        return t
    roots=[];js=set()
    for x in product(range(p),repeat=2):
        H=(0,0)
        for k in range(6,-1,-1): H=a2(m2(H,x),(comb(6,k)**2%p,0))
        if H!=(0,0): continue
        roots.append(x)
        D=m2(pw2(x,2),pw2(a2(x,(-1,0)),2))
        Z=pw2(a2(a2(pw2(x,2),(-x[0],-x[1])),(1,0)),3)
        js.add(m2(m2((256%p,0),Z),pw2(D,p*p-2)))
    assert len(roots)==6 and js=={(5,0)}
    At,Bt=(4*A0%p,8*B0%p)
    assert (At,Bt)==(7,4) and count(p,At,Bt)==12
    g=(12,3)
    Ax,Bx=V(At,Bt,*g)
    K=(3,2)
    assert (Ax,Bx)==(11,9) and count(p,Ax,Bx)==12
    assert V(Ax,Bx,*K)==(3**4*At%p,3**6*Bt%p)
    # x_fibre solves [X-3^2*g_x](X-K_x)^2+2(3K_x²+Ax)(X-K_x)+4K_y².
    r1,gx=K[0],g[0]
    constant=(2*(3*r1*r1+Ax))%p
    f=[(-9*gx*r1*r1-constant*r1+4*K[1]**2)%p,
       (r1*r1+18*gx*r1+constant)%p,
       (-2*r1-9*gx)%p,1]
    assert all(ev(f,x) for x in range(p))
    # F_13[X]/f: z^3 = -f0-f1 z-f2 z^2.
    def z(x):return (x%p,0,0)
    def a(x,y):return tuple((u+v)%p for u,v in zip(x,y))
    def n(x):return tuple(-u%p for u in x)
    def b(x,y):return a(x,n(y))
    def m(x,y):
        c=[0]*5
        for i,u in enumerate(x):
            for j,v in enumerate(y):c[i+j]+=u*v
        for i in (4,3):
            for j in range(3):c[i-3+j]-=c[i]*f[j]
        return tuple(v%p for v in c[:3])
    def e(x,i):
        t=z(1)
        while i:
            if i&1:t=m(t,x)
            x=m(x,x);i//=2
        return t
    def d(x,y):
        assert y!=z(0)
        return m(x,e(y,p**3-2))
    def ec(P,Q):
        (x,y),(u,v)=P,Q
        j=d(a(m(z(3),e(x,2)),z(Ax)),m(z(2),y)) if P==Q else d(b(v,y),b(u,x))
        s=b(b(e(j,2),x),u)
        return s,b(m(j,b(x,s)),y)
    X=(0,1,0)
    T=b(X,z(r1))
    dx=b(b(z(1),d(z(constant),e(T,2))),d(z(8*K[1]**2),e(T,3)))
    Y=d(z(27*g[1]),dx)
    assert e(Y,2)==a(a(e(X,3),m(z(Ax),X)),z(Bx))
    xo=d(a(a(X,d(z(constant),T)),d(z(4*K[1]**2),e(T,2))),z(9))
    yo=d(m(Y,dx),z(27))
    assert (xo,yo)==(z(g[0]),z(g[1]))
    P=(X,Y)
    KP=(z(K[0]),z(K[1]))
    KM=(z(K[0]),z(-K[1]))
    F=tuple(e(u,p) for u in P)
    F2=tuple(e(u,p*p) for u in P)
    assert F==ec(P,KM) and F2==ec(P,KP)
    print(json.dumps({
      'Eflat_F13':16,'Eflat_F169':192,'Eflat_antispace_order':12,
      'Eflat_F61_torsion_exclusion':68,'source_geometric_ss_j':5,'source_label_total':mu,
      'short_Eflat_coeff':(A0,B0),'short_anti_twist_coeff':(At,Bt),
      'short_local_quotient_coeff':(Ax,Bx),'target_order_three':g,
      'dual_kernel_generator':K,'dual_fibre_cubic_ascending':f,
      'dual_fibre_point':P,'arithmetic_F13_translation':'-K',
      'arithmetic_F169_translation':'+K'},indent=2,sort_keys=True))
if __name__=='__main__': main()
