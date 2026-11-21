#!/usr/bin/env python3
"""D=-119 actual unit-2-arm tame x0(3) CM packet, exact finite lifts."""
from itertools import product
from functools import lru_cache
import json
K=14; M=1<<K; F=(1,0,1,0,0,1)  # S^5+S^2+1
zero=(0,)*5
def c(a):return (a%M,0,0,0,0)
def add(a,b):return tuple((x+y)%M for x,y in zip(a,b))
def sc(a,i):return tuple(x*i%M for x in a)
def sub(a,b):return add(a,sc(b,-1))
def mu(a,b):
    r=[0]*9
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    for j in range(8,4,-1):
        r[j-5]-=r[j]
        r[j-3]-=r[j]
    return tuple(x%M for x in r[:5])
def pw(a,i):
    if i<0:return pw(inv(a),-i)
    q=c(1)
    while i:
        if i&1:q=mu(q,a)
        i//=2
        if i:a=mu(a,a)
    return q
def red(a):return tuple(x%2 for x in a)
@lru_cache(None)
def inv(a):
    assert red(a)!=zero
    b=pw(red(a),30)
    assert red(mu(a,b))==red(c(1))
    for _ in range(5):b=mu(b,sub(c(2),mu(a,b)))
    assert mu(a,b)==c(1)
    return b
def di(a,b):return mu(a,inv(b))
def newton(a,fn,df):
    for _ in range(5):a=sub(a,di(fn(a),df(a)))
    assert fn(a)==zero
    return a
S=(0,1,0,0,0)
assert red(pw(S,31))==red(c(1)) and red(S)!=red(c(1))
assert all(red(pw(S,i))!=red(c(1)) for i in range(1,31))
T=newton(pw(S,2),lambda x:add(add(pw(x,5),pw(x,2)),c(1)),
                    lambda x:add(sc(pw(x,4),5),sc(x,2)))
TP=[pw(T,i) for i in range(5)]
def frob(x):
    a=zero
    for q,t in zip(x,TP):a=add(a,sc(t,q))
    return a
def fro(x,n):
    for _ in range(n):x=frob(x)
    return x
assert fro(S,5)==S
fr=[red(pw(S,i)) for i in range(1,31)]
js=lambda u:mu(mu(add(u,c(27)),pw(add(u,c(243)),3)),pw(u,-3))
jt=lambda u:mu(mu(add(u,c(27)),pw(add(u,c(3)),3)),pw(u,-1))
jsred={u:red(js(u)) for u in fr}; jtred={u:red(jt(u)) for u in fr}
b={}
for u in fr:
   q0=red(pw(u,4)); q1=red(inv(u))
   for v in fr:
       if v==q1 or jsred[v]!=jtred[u]:continue
       if red(inv(v))==q0 or jsred[q0]!=jtred[v]:continue
       # Make sure this is ordinary and keep all (u,v) possibles.
       b.setdefault(u,[]).append(v)
assert len(b)==10 and all(len(v)==1 for v in b.values())
def j2s(t):return mu(pw(add(t,c(256)),3),pw(t,-2))
def js2prime(t):
    b=add(t,c(256))
    return sub(sc(mu(pw(b,2),pw(t,-2)),3),sc(mu(pw(b,3),pw(t,-3)),2))
def j2t(t):return mu(pw(add(t,c(16)),3),pw(t,-1))
def t2(j):return newton(red(j),lambda t:sub(j2s(t),j),js2prime)
def can(j):
    v=j
    for _ in range(K):v=fro(j2t(t2(v)),4)
    assert frob(v)==j2t(t2(v))
    return v
def jprime(u):
    a=add(u,c(27));b=add(u,c(243))
    return add(add(mu(pw(b,3),pw(u,-3)),sc(mu(mu(a,pw(b,2)),pw(u,-3)),3)),
               sc(mu(mu(a,pw(b,3)),pw(u,-4)),-3))
def rootx(X):
    X2=pw(X,2);X22=add(X2,inv(X2))
    return newton(X2,lambda x:sub(sub(pw(x,2),mu(x,X22)),c(3)),lambda x:sub(sc(x,2),X22))
def tame(X):
    x=rootx(X);yy=mu(pw(X,2),x); x24=add(c(1),x)
    num=add(add(mu(pw(X,2),yy),sc(pw(X,2),3)),sub(pw(yy,2),yy))
    y24=di(num,mu(X,sub(yy,c(1))))
    t12=sub(di(y24,sub(x24,c(2))),c(3))
    t6=di(pw(t12,2),add(t12,c(2)))
    return di(mu(pw(t6,2),add(t6,c(9))),pw(add(t6,c(8)),2))
def chart(u):
    X=u
    for _ in range(K):X=add(u,sub(X,tame(X)))
    assert tame(X)==u
    return X,rootx(X)
# Integral formal omega coefficients in t=z², from S=1−2tS−3t²S².
J=K//2
ss=[1]
for n in range(1,J+1):
    ss.append(-2*ss[n-1]-3*sum(ss[i]*ss[n-2-i] for i in range(n-1)))
bb=[0]
for n in range(1,J+1):
    bb.append(n*ss[n]-sum(bb[i]*ss[n-i] for i in range(1,n)))
def log(u):
    X,x=chart(u);y=mu(sub(X,inv(X)),x)
    a=add(pw(x,2),c(3));b=sub(sub(sc(pw(x,2),3),sc(x,4)),c(3))
    w=di(mu(y,pw(a,2)),add(sub(sc(pw(y,4),8),sc(mu(mu(b,x),pw(y,2)),4)),mu(b,pw(a,2))))
    val=w
    for j in range(1,J+1):val=add(val,sc(pw(w,2*j+1),pow(2,2*j,M)*bb[j]*pow(2*j+1,-1,M)))
    return val
# One Frob² orbit is in each χ17 half; the arithmetic 2-Frobenius has order 5.
def orbit(u):
    return {red(fro(u,i)) for i in range(5)}
a=min(b); aa=orbit(a); bb0=orbit(b[a][0]); assert len(aa)==len(bb0)==5 and set(b)==aa|bb0 and not aa&bb0
rows=[];sums=[]
for candidate in (a,b[a][0]):
    j=can(jsred[candidate]);u=newton(candidate,lambda u:sub(js(u),j),jprime)
    w=log(u);s0=zero
    for i in range(5):s0=add(s0,fro(w,i))
    assert all(c0==0 for c0 in s0[1:])
    sums.append(s0[0]); rows.append(dict(tame_residue=candidate,j=j,u=u,log=w,half_log=s0[0]))
data=dict(k=K, ring='(Z/2^k)[S]/(S^5+S^2+1)', norm36_relation_exponent=2, half_rows=rows,
          raw_log=sum(sums)%M, weighted_log=(sums[0]-sums[1])%M)
assert sums==[264,11824] and data["raw_log"]==12088 and data["weighted_log"]==4824
print(json.dumps(data,indent=2,sort_keys=True))
