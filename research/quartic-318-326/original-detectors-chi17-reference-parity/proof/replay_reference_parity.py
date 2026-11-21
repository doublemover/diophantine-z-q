"""Exact F_3[X] replay for the D=-119 weighted trace. Standard library."""
import json
from math import gcd, isqrt

P=3
def canon(x):
    y=[i%P for i in x]
    while y and not y[-1]:y.pop()
    return tuple(y)
X=(0,1); ONE=(1,)
def add(a,b):
    return canon((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b))))
def sc(a,c):return canon(c*x for x in a)
def sub(a,b):return add(a,sc(b,-1))
def mul(a,b):
    if not a or not b:return ()
    t=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        if u:
            for j,v in enumerate(b):t[i+j]+=u*v
    return canon(t)
def frob(a,k=1):
    if not a:return ()
    q=3**k; t=[0]*(q*(len(a)-1)+1)
    for i,u in enumerate(a):t[q*i]=u
    return canon(t)
def qr(a,b):
    assert b
    x=list(a);c=pow(b[-1],-1,3); q=[0]*max(0,len(a)-len(b)+1)
    while len(x)>=len(b):
        k=len(x)-len(b); u=x[-1]*c%3;q[k]=u
        if u:
            for j,v in enumerate(b):x[j+k]=(x[j+k]-u*v)%3
        while x and not x[-1]:x.pop()
    return canon(q),tuple(x)
def rem(a,b):return qr(a,b)[1]
def pd(a,b):
    while b:a,b=b,rem(a,b)
    return sc(a,pow(a[-1],-1,3)) if a else ()
def power(a,n,b):
    c=ONE
    while n:
        if n&1:c=rem(mul(c,a),b)
        n//=2
        if n:a=rem(mul(a,a),b)
    return c
def fn(a,n,b):
    for _ in range(n):a=rem(frob(a),b)
    return a
def norm(a,b,subdegree=2,degree=5):
    prod=ONE
    for _ in range(degree):
        prod=rem(mul(prod,a),b)
        a=fn(a,subdegree,b)
    return prod
def step(pair,m,second):
    n,d=pair
    l=(1,2,1)[m] if second else (2,1,1)[m]
    w=add(n,sc(d,l))
    return (mul(n,w),mul(d,d)) if second else (mul(n,n),mul(w,d))
def edges(k):
    f=(X,ONE)
    for m in range(3):f=step(f,m,m<k)
    assert pd(*f)==ONE
    return f

A=[edges(k) for k in range(4)]
eq=[sub(mul(n,frob(d0,4)),mul(d,frob(n0,4))) for (n0,d0),(n,d) in zip(A,A[1:])]
g=pd(pd(eq[0],eq[1]),eq[2])
assert len(g)==169
g=pd(g,sub(fn(X,10,g),X))
h=canon([1,0,-1,-1,1,1,1,1,1,-1,1])
n=(1,0,1);d=(2,2,1)
assert g==mul(mul(mul(X,n),d),h)
assert fn(X,10,h)==X
assert pd(h,sub(fn(X,5,h),X))==pd(h,sub(fn(X,2,h),X))==ONE
assert len(n)==len(d)==3 and all((j*j+1)%3 and (j*j-j-1)%3 for j in range(3))
# Exclude the t=0 cusp, and verify that the remaining quadratic roots
# give t_2=-1, hence j=0. The H10 polynomial is prime to every denominator.
assert rem(A[0][0],X)==() and rem(A[0][1],X)==ONE
for z in (n,d):
    assert pd(A[0][1],z)==ONE and rem(add(*A[0]),z)==()
assert all(pd(den,h)==ONE for _,den in A) and pd(add(*A[0]),h)==ONE
# g(t16)=(t16^2+1)/(t16^2-t16-1), on the good ordinary plus component.
u=norm(mul(n,power(d,3**10-2,h)),h)
assert fn(u,2,h)==u and power(u,4,h)==(2,)
minus_phase=power(u,6,h) # u/u^3=u^6 since u^8=1
assert power(minus_phase,2,h)==(2,) and power(minus_phase,4,h)==ONE
def forms(N):
    return [(a,b,(b*b+N)//(4*a)) for a in range(1,isqrt(N//3)+1)
            for b in range(-a,a+1) if (b*b+N)%(4*a)==0 and
            (c:=(b*b+N)//(4*a))>=a and gcd(gcd(a,b),c)==1 and
            (b>=0 or a!=c and -b!=a)]
assert [len(forms(n)) for n in (23,47,71,95,119)]==[3,5,7,8,10]
assert (3*3+119)//4==32 and (5*5+119)//4==36
print(json.dumps(dict(
    scope="exact D=-119 reference only; v2(m7)=0; no target unweighted trace",
    class_numbers={i:len(forms(i)) for i in (23,47,71,95,119)},
    class_119_forms=forms(119), edges_num_den=A, pre_gcd_degree=168,
    finite_gcd=g, H10=h, norm_to_F9=u, norm_fourth=power(u,4,h),
    weighted_torus=minus_phase, weighted_torus_squared=power(minus_phase,2,h)),
    indent=2,sort_keys=True))
