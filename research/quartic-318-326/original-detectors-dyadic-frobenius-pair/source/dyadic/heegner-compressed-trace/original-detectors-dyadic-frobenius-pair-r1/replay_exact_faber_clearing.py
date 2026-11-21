"""Exact Faber repair at the source cusp; no CM row is evaluated."""
from collections import defaultdict
from math import comb
import json

D=20
def add(a,b):
    return {i:x for i in a.keys()|b.keys() if (x:=a.get(i,0)+b.get(i,0))}
def scale(a,b):
    return {i:x*b for i,x in a.items() if x*b}
def constant(x):
    return {0:x} if x else {}
def shift(a,s):
    return {i+s:x for i,x in a.items() if -D<=i+s<=D}
def mul(a,b):
    r=defaultdict(int)
    for i,x in a.items():
        for j,y in b.items():
            if -D<=i+j<=D:
                r[i+j]+=x*y
    return {i:x for i,x in r.items() if x}
def pw(a,n):
    r={0:1}
    for _ in range(n):
        r=mul(r,a)
    return r
def summands(items):
    r={}
    for a in items:
        r=add(r,a)
    return r
def inv(a):
    k=min(a)
    a=shift(a,-k)
    assert a[0]==1
    neg_tail=add(constant(1),scale(a,-1))
    return shift(summands(pw(neg_tail,j) for j in range(D+1)),-k)
def compose(a,b):
    return summands(scale(pw(b,i),x) for i,x in a.items())
def coords(a,i,j):
    return [a.get(k,0) for k in range(i,j)]

t={0:1}
for level,power in ((1,5),(3,1),(2,-1),(6,-5)):
    for i in range(level,D+1,level):
        if power>=0:
            poly={i*j:(-1)**j*comb(power,j) for j in range(min(power,D//i)+1)}
        else:
            poly={i*j:comb(-power+j-1,j) for j in range(D//i+1)}
        t=mul(t,poly)
t=shift(t,-1)
A=add(t,constant(9))
S=add(A,scale(inv(A),9))
J=mul(add(pw(S,2),constant(-36)),inv(add(S,constant(-10))))
T=mul(pw(add(S,constant(6)),3),pw(inv(add(S,constant(-10))),2))
F=mul(pw(add(S,constant(-6)),3),inv(add(S,constant(-10))))
assert coords(T,-1,3)==[1,42,783,8672]
assert coords(F,-2,7)==[T.get(i//2,0) if i%2==0 else 0 for i in range(-2,7)]
assert J[-1]==1 and min(J)==-1
b=coords(compose({1:26593280,2:7859776,3:26851175},T),-3,0)[::-1]
assert b==[205856642639,3391107826,26851175]

P=[constant(1)]
for j in range(1,7):
    p={j:1}
    for k in range(j-1,-1,-1):
        p=add(p,scale(P[k],-compose(p,J).get(-k,0)))
    assert coords(compose(p,J),-j,1)==[1]+[0]*j
    P.append(p)
f=summands(scale(add(P[2*j],scale(P[j],-1)),b[j-1]) for j in range(1,4))
old={i:c for i,c in enumerate([24790720,8290800,10177780,11909401,14213408,26202676,26851175])}
assert all(x%(1<<25)==0 for x in add(f,scale(old,-1)).values())
polar=compose(f,J)
assert polar.get(0,0)==0
for chi3 in (-1,0,1):
    for chi5 in (-1,0,1):
        # Everywhere here chi(2)=+1.
        chi=(0,1,1,chi3,1,chi5,chi3)
        for k in (1,3,5):
            assert sum(chi[j]*polar.get(-k*j,0) for j in range(1,7))==0
print(json.dumps(dict(faber=[coords(p,0,7) for p in P],
                      repaired_polynomial=coords(f,0,7),
                      b_ascending=b, principal_ascending=coords(polar,-6,1),
                      scope="exact principal part repair; no CM trace or product evaluated"),
                 sort_keys=True,indent=2))

