"""Exact rational replay of the actual D=210 twists. Python standard library."""
from fractions import Fraction as Q
from itertools import permutations
from math import isqrt, prod
import json

B = (0,32,76832,-343)
inertia = (105,70,42,30,210)
rows = (
    ((3,5,7),"210b6",(1,0,1,-21953,-1253644),(Q(-345,4),-85,171)),
    ((2,5,7),"210c3",(1,1,1,-1050,-13533),(Q(-77,4),-19,37)),
    ((2,3,7),"210a6",(1,0,0,-2701,-52819),(-34,-26,Q(239,4))),
    ((2,3,5),"210e5",(1,0,0,-120050,-16020000),(Q(-801,4),-200,400)),
    ((6,10,14),"210d2",(1,1,0,-23,33),(-6,2,Q(11,4))),
)

def mul(x,y):
    z=[Q(0)]*(len(x)+len(y)-1)
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            z[i+j]+=a*b
    return tuple(z)

def linear(a,b):
    return (Q(b),Q(a))

def dmul(x,y):
    from math import gcd
    return x*y//gcd(x,y)**2

def sqclass(r):
    n=abs(r.numerator*r.denominator)
    v=-1 if r<0 else 1
    for p in range(2,isqrt(n)+1):
        if p*p>n: break
        e=0
        while n%p==0:
            n//=p
            e+=1
        if e%2: v*=p
    return n*v

def square(r):
    return r>0 and isqrt(r.numerator)**2==r.numerator and isqrt(r.denominator)**2==r.denominator

out=[]
for j,(gens,label,ai,roots) in enumerate(rows):
    subgroup={1}
    for g in gens:
        subgroup |= {dmul(g,h) for h in subgroup}
    assert len(subgroup)==8
    assert tuple(m in subgroup for m in inertia)==tuple(i==j for i in range(5))
    a1,a2,a3,a4,a6=ai
    F=(a6+Q(a3*a3,4),a4+Q(a1*a3,2),a2+Q(a1*a1,4),Q(1))
    assert F==mul(mul(linear(1,-roots[0]),linear(1,-roots[1])),linear(1,-roots[2]))
    src=[Q(b) for i,b in enumerate(B) if i!=j] if j<4 else [Q(1,b) for b in B[1:]]
    hits=[]
    for rr in permutations(roots):
        A=Q(rr[1]-rr[0],src[1]-src[0])
        D=rr[0]-A*src[0]
        if A*src[2]+D==rr[2]: hits.append((A,D,rr))
    assert len(hits)==1
    A,D,rr=hits[0]
    if j<4:
        U=mul(mul(linear(A,D-rr[0]),linear(A,D-rr[1])),linear(A,D-rr[2]))
        tgt=mul(mul(linear(1,-src[0]),linear(1,-src[1])),linear(1,-src[2]))
        raw=A**3
        assert U==tuple(raw*z for z in tgt)
    else:
        U=mul((0,1),mul(mul(linear(D-rr[0],A),linear(D-rr[1],A)),linear(D-rr[2],A)))
        tgt=mul(mul(linear(1,-B[0]),linear(1,-B[1])),mul(linear(1,-B[2]),linear(1,-B[3])))
        raw=-A**3/prod(B[1:])
        assert U==tuple(raw*z for z in tgt)
    k=sqclass(raw)
    assert square(raw/k)
    out.append({"omit":j,"kernel_generators":gens,"cremona":label,"a_invariants":ai,
                "roots":list(map(str,roots)),"A":str(A),"B":str(D),
                "raw":str(raw),"K":k})
classes=[r["K"] for r in out]
c=[sqclass(Q(k*classes[4])) for k in classes[:4]]
assert classes==[3,7,-1,2,-42] and c==[-14,-6,42,-21]
assert all(square(Q(prod(c[i] for i in range(4) if i!=j),classes[j])) for j in range(5))
print(json.dumps({"coordinate":"t=32*s","contacts":B, "inertia":inertia,
                  "sections":out,"twists":c},indent=2))
