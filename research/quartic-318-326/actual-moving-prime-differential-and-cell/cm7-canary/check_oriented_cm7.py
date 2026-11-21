#!/usr/bin/env python3
"""Rational polynomial reduction of an actual oriented ramified CM endomorphism."""
from fractions import Fraction as F
import json

def trim(a):
    a=list(map(F,a))
    while a and a[-1]==0:a.pop()
    return tuple(a)
def add(*polys):
    n=max(map(len,polys),default=0)
    return trim(sum((y[i] if i<len(y) else 0) for y in polys) for i in range(n))
def scale(a,c):return trim(c*d for d in a)
def mul(a,b):
    z=[F(0)]*(len(a)+len(b))
    for i,u in enumerate(a):
        for j,v in enumerate(b):z[i+j]+=u*v
    return trim(z)
def fac(*a):
    z=(F(1),)
    for q in a:z=mul(z,q)
    return z
def powp(a,n):return fac(*([a]*n))
def diff(a):return trim(i*a[i] for i in range(1,len(a)))
def mod(a,b):
    assert b
    while a and len(a)>=len(b):
        a=add(a,(0,)*(len(a)-len(b))+scale(b,-a[-1]/b[-1]))
    return a
def coprime(a,b):
    while b:a,b=b,mod(a,b)
    return len(a)==1
def dump(a):return [str(z) for z in a]
def residue(q):
    a,b=q.numerator,q.denominator
    e=0
    while a%7==0:a//=7;e+=1
    while b%7==0:b//=7;e-=1
    return e,a*pow(b,-1,7)%7
def red(a,shift):
    z=[]
    for i,q in enumerate(a):
        if q:
            e,r=residue(q)
            z.append((i+2*e-shift,i,((-1 if e%2 else 1)*r)%7))
    m=min(t[0] for t in z)
    out=[0]*len(a)
    for e,i,r in z:
        if e==m:out[i]=r
    return m,trim(out)
def f7(a):return trim(int(c)%7 for c in a)

x=(0,1)
A,B=-F(35,16),-F(49,32)
f=(B,A,0,1)
g=(-F(91,64),-F(21,16),F(7,4),1)
psi3=(-A*A,12*B,6*A,0,3)
psi4scalar=(-8*B*B-A**3,-4*A*B,-5*A*A,20*B,5*A,0,1)
psi5=add(scale(fac(powp(f,2),psi4scalar),32),scale(powp(psi3,3),-1))
psi7=add(mul(psi5,powp(psi3,3)),scale(fac(powp(f,2),powp(psi4scalar,3)),-128))
assert mod(psi7,g)==() and coprime(g,f) and coprime(g,diff(g))
assert F(1728)*4*A**3/(4*A**3+27*B**2)==-3375
D=scale(f,4)
N=add(powp((A,0,3),2),scale(mul(x,D),-2))
assert mod(add(*(scale(fac(powp(N,j),powp(D,3-j)),g[j]) for j in range(4))),g)==()
# Newton sums for the 3 opposite-pair x values.
p1=-g[2]; p2=-g[2]*p1-2*g[1]; p3=-g[2]*p2-g[1]*p1-3*g[0]
tv=2*(3*p2+3*A)
wv=2*(5*p3+3*A*p1+6*B)
assert A-5*tv==49*A and B-7*wv==-343*B

# x_phi / normalized differential from V elu, in the original x coordinate.
G=diff(g)
S2=add(mul(powp(x,2),G),scale(mul((p1,3),g),-1))
T=add(mul(f,G),scale(mul((p2+3*A,p1,3),g),-1))
D0=powp(g,2)
N0=add(mul(x,D0),mul(scale(add(scale(S2,3),scale(G,A)),2),g),
       scale(add(mul(diff(T),g),scale(mul(T,G),-1)),-4))
ND=add(mul(diff(N0),D0),scale(mul(N0,diff(D0)),-1))
DD=powp(D0,2)
# Via x_orig=pi*x_good and pi^2=-7, oriented [pi] takes
# x_good -> x_phi(pi*x_good)/pi^3,
# y_good -> y_good*x_phi'(pi*x_good)/pi^3.
rx,dx=red(N0,3),red(D0,0)
ry,dy=red(ND,3),red(DD,0)
assert rx[0]==dx[0] and ry[0]==dy[0]
assert f7(rx[1])==f7(mul(powp(x,7),dx[1]))
assert f7(ry[1])==f7(mul(scale(powp((0,-1,0,1),3),-1),dy[1]))
assert residue(F(5,16))[1]==6 and residue(-F(3,32))[1]==1
print(json.dumps({'kernel_monic':dump(g),'velu_newton_sums':dump((p1,p2,p3)),
     'velu_t_w':dump((tv,wv)),'deterministic_reduced_x':'x^7',
     'deterministic_reduced_y':'-y^7',
     'reduce_x_num_den':[[e,dump(a)] for e,a in (rx,dx)],
     'reduce_y_multiplier_num_den':[[e,dump(a)] for e,a in (ry,dy)],
     'good_curve_mod7_A':6,'good_curve_Hasse_coefficient_over_pi':1,
     'reduced_oriented_formal_x7_coefficient':6,'u=Delta/p':-1},indent=2))
