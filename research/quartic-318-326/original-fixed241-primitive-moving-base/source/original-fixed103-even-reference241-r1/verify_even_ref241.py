#!/usr/bin/env python3
from fractions import Fraction as Q
from math import isqrt, factorial, prod, gcd
import json

f=241; B=5000; M=2**80
assert all(f%d for d in range(2,isqrt(f)+1)) and f%24==1
deltas=(2,4,6,12)
assert sum(deltas)==sum(24//d for d in deltas)==24 and prod(deltas)==24**2
assert sum(sum(gcd(j,a)==1 for j in range(1,a+1)) for a in
    [gcd(d,24//d) for d in range(1,25) if 24%d==0])==8
e=[0]*(B+1);e[0]=1
for d in deltas:
    v=[0]*(B+1);j=0
    while d*j*(3*j-1)//2<=B:
        for k in ((0,) if j==0 else (j,-j)):
            nu=d*k*(3*k-1)//2
            if nu>B:continue
            sign=-1 if j%2 else 1
            for n in range(nu,B+1):v[n]+=sign*e[n-nu]
        j+=1
    e=v

def arctans(t,N):return sum(((-1)**k*Q(1,(t**(2*k+1))*(2*k+1)) for k in range(N)),Q(0))
pl=16*arctans(5,24)-4*arctans(239,25)
pu=16*arctans(5,25)-4*arctans(239,24)
P=10**16;u=isqrt(48*P*P)
tl,tu=2*pl/(f*Q(u+1,P)),2*pu/(f*Q(u,P))
v=lambda x,k:sum(((-x)**j/Q(factorial(j)) for j in range(k+1)),Q(0))
lo=(v(tu,9)*M).__floor__();hi=(v(tl,8)*M).__ceil__()
assert 0<lo<hi<M

def chi(n):
    if n%2==0 or n%f==0:return 0
    a=pow(n%f,(f-1)//2,f)
    assert a in (1,f-1)
    return (-1 if n%4==3 else 1)*(1 if a==1 else -1)

x=y=M
S=T=0
for n in range(1,B+1):
    x=x*lo//M
    y=-(-y*hi//M)
    a=2*chi(n)*e[n-1]
    S+=min(a*x,a*y)//n;T+=-(-max(a*x,a*y)//n)
y=-(-y*hi//M)
tail=-(-(4*y*M)//(M-hi))
L,R=S-tail,T+tail
assert Q(34748,10000) < Q(L,M) < Q(R,M) < Q(34749,10000)
print(json.dumps(dict(f=f,conductor=48*f*f,terms=B,scale=M,
    q_dyadic=[lo,hi],partial_dyadic=[S,T],tail_dyadic=tail,central_interval=[L,R],
    simple_bounds=['3.4748','3.4749']),indent=2))
