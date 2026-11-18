"""Exact elementary controls for the two memos. Python 3 standard library."""
from fractions import Fraction as F
from math import isqrt
import json

def eta0(E):
    # squared rational multiplier and coefficient in exp(-pi/(12v)*k)
    a,b=F(1),F(0)
    for k,n in E.items():
        a*=F(k)**(-n)
        b+=F(n,k)
    return str(a),str(b)

def prime(n):
    return n>1 and all(n%j for j in range(2,isqrt(n)+1))
def quart(a,p):
    t=pow(a,(p-1)//4,p)
    assert t in (1,p-1)
    return 1 if t==1 else -1
def sample(theta):
    q=127 if theta==409 else 1087
    assert prime(theta) and prime(q) and q%24==7
    rows=[]
    for f in (1,2):
        r=next(j for j in range(7,24*17,24) if j%17==(f*q)%17)
        j=next(j for j in range(r,24*17*theta,24*17) if j%theta==q%theta)
        new=j
        while new<=q or not prime(new): new+=24*17*theta
        assert new%24==7 and new%theta==q%theta and new%17==(f*q)%17
        x,y=quart(new,17),quart(new*theta,17)
        assert x*y==quart(theta,17)
        rows.append([f,new,x,y])
    assert rows[1][2:]==[-z for z in rows[0][2:]]
    return dict(theta=theta,old=q,rows=rows)
def a(P): m,b=P;return -m,b
def s(P): m,b=P;return -m,(b+m)%2
def plus(P,Q):return P[0]+Q[0],(P[1]+Q[1])%2
for m in range(-8,9):
    for b in range(2):
        P=m,b
        assert a(s(P))==s(a(P)) and a(a(P))==s(s(P))==P
Q=(1,0)
assert plus(Q,s(Q))==(0,1) and plus(Q,a(Q))==(0,0)
eta = {name:eta0(E) for name,E in {'f':{2:1,4:1,6:1,12:1},'B':{4:1,8:1,12:1,24:1},'g':{4:4,12:4,2:-1,6:-1,8:-1,24:-1}}.items()}
assert eta=={'f':('1/576','1'),'B':('1/9216','1/2'),'g':('1/2304','1/2')}
print(json.dumps(dict(eta_squared_multipliers_and_exponents=eta,strict_CRT=[sample(409),sample(457)],abstract_norm=plus(Q,a(Q)),abstract_reflection=plus(Q,s(Q))),indent=2))
