#!/usr/bin/env python3
"""Independent p=17 reciprocal scales, all sign phases, and local F repair."""
from fractions import Fraction as Q
from pathlib import Path
from math import prod
from itertools import product
import json,sys
A=json.loads(Path(sys.argv[1]).read_bytes())
B=json.loads(Path(sys.argv[2]).read_bytes())
p=17;m=p*p
J=int(B['literal_J']); assert J==A['retuned_literal_J']
s=1+6**15*3**65536*J; k=2*(s-2)
def mat(x,y,n):
    a,b,c,d=x
    e,f,g,h=y
    return ((a*e+b*g)%n,(a*f+b*h)%n,(c*e+d*g)%n,(c*f+d*h)%n)
def uv(z,N):
    H=(0,1,N-1,z%N); R=(1,0,0,1)
    for i in bin(k)[2:][::-1]:
        if i=='1':R=mat(H,R,N)
        H=mat(H,H,N)
    return R[1],R[3]
def r(x,n):
    x=Q(x); return x.numerator*pow(x.denominator,-1,n)%n
def rm(a):
    return r(a,m)
def v(a):
    if not a:return None
    a=Q(a); n,d=a.numerator,a.denominator;z=0
    while n%p==0:n//=p;z+=1
    while d%p==0:d//=p;z-=1
    return z
def ch(a):
    t=pow(r(a,p),8,p)
    return -1 if t==16 else t
def arm(rho):
    R=(1+rho,2*rho); D=(3-rho)**2
    def add(P,Q):
        if len(P)==1:
            if len(Q)==1:return ((P[0]+Q[0])%m,)
            z=P[0];x,y=Q
            return ((x+2*y*z)%m,(y+(3*x*x-D)*z)%m)
        if len(Q)==1:return add(Q,P)
        x,y=P;u,t=Q
        h=u*u+u*x+x*x-D
        if (u-x)%p:w=rm(QQ(t-y,u-x,m))
        elif (t-y)%p:return (rm(QQ(u-x,t-y,m)),)
        elif (t+y)%p:w=rm(QQ(h,t+y,m))
        else:return (rm(QQ(t+y,h,m)),)
        xx=(w*w-x-u)%m
        return (xx,(w*(x-xx)-y)%m)
    def point(n):
        P=(0,)
        for _ in range(n):P=add(P,R)
        return P
    for order in range(1,2*p+2):
        if len(point(order))==1:break
    N=p*order; d=s-2; g=1
    while d%2==0 and N%2==0:d//=2;g*=2
    while d%5==0 and N%5==0:d//=5;g*=5
    while d%p==0:d//=p;g*=p
    u,ww=uv(s,N*g)
    assert not u%g
    labels=[3723%N,s%N,ww%N,u//g*pow(d,-1,N)%N]
    # Avoid normalizing any order modulo p^2 to the size of an arm.
    xs=[point(j) for j in labels]
    assert all(len(P)==2 for P in xs)
    abscissae=[r(Q(2*y)*pow((x*x+D)%m,-1,m),m) for x,y in xs]
    return (order,labels,abscissae,pow(prod(abscissae)%m,-1,m))
def QQ(a,b,m):return (a*pow(b,-1,m))%m
for rec in A['arms']:
    rho=next(i for i in range(rec['r'],m,p) if i*i%m==2)
    assert rho==rec['rho']
    order,labels,U,a=arm(rho)
    assert (order,labels,U,a)==(rec['order'],rec['labels'],rec['U_p2'],rec['A'])
a1,a2=[t['A'] for t in A['arms']]
c=[1,((a1+a2)*pow(2,-1,m)+a1*a2)%m,a1*a2%m]
assert c==A['c_mod_p2']==[1,216,84] and v(c[2]**2-1)==1
s0,t0=Q(-32,407),Q(1,2399)
roots=(0,Q(-1,2),-1,s0,t0)
pol=lambda x:prod(x-r for r in roots)
rel=[r(Q(d,c[1])**2,p) for d in c]
assert rel==[15,1,15]
compatible={}
for phase in product((-1,1),repeat=2):
    out=[]
    for X in sorted({z*z%p for z in range(1,p)}):
        if any(vv and vv!=sg for vv,sg in zip((ch(X-s0),ch(X-t0)),phase)):continue
        Ts=[z*X%p for z in rel]
        Fsigns=[ch(pol(T)) for T in Ts]
        outer_common_simple_root=Ts[0] in [r(j,p) for j in roots] and Ts[0]==Ts[2]
        outcome='nonsquare unit' if -1 in Fsigns else 'forced odd outer root depth' if outer_common_simple_root else 'survives'
        out.append(dict(X=X,T=Ts,Fsigns=Fsigns,outcome=outcome))
    compatible[str(phase)]=out
assert all(all(x['outcome']!='survives' for x in compatible[str((asgn,-1))]) for asgn in (-1,1))
assert [x['X'] for x in compatible[str((-1,1))] if x['outcome']=='survives']==[8]
assert [ch(B[z]) for z in ('a','b')]==[-1,-1] and [r(B[z],p) for z in ('a','b')]==A['a_b_mod_p']
W=566; X=W*W
assert [ch(X-s0),ch(X-t0)]==[-1,1]
assert v(pol(X))==2 and ch(pol(X)/p**2)==1
fixed_T=[r(Q(d,c[1])**2*X,m) for d in c]
assert fixed_T==[256,144,86]
assert all(ch(pol(T))==1 and v(T-1)==1 for T in fixed_T[::2])
report=dict(c_mod289=c,c2square_minus_1_depth=1,phase_unit_cases=compatible,
            smallest_squareclass_repair={'W':W,'fixed_T_mod289':fixed_T,'v17_mid_F':2,'mid_F_unit':r(pol(X)/p**2,p),
                                         'outer_Delta_depths':[1,1],'necessary_outer_trace_depths':[4,4]})
print(json.dumps(report,indent=2))
