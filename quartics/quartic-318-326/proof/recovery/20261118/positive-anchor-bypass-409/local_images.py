"""Independent small complete local-image computation for either sign of the torsion anchor."""
from fractions import Fraction as F
from itertools import product
from math import prod
def val(p,n):
    k=0
    while n%p==0:n//=p;k+=1
    return k,n
def cls(x,p):
    x=F(x);assert x
    if p==0:return int(x<0)
    a,u=val(p,x.numerator);b,v=val(p,x.denominator);o=(a-b)%2
    if p==2:
        w=(u*v)%8
        return o + 2*(w in (3,7)) + 4*(w in (3,5))
    return o+2*(pow(u*v%p,(p-1)//2,p)==p-1)
def pair(x,y,p):return cls(x,p) + (cls(y,p)<<3)
def img(roots,p):
    S={0}
    def add(k):
        nonlocal S
        S=S|{s^k for s in S}
    for r in roots:
        a,b=(r-e if r!=e else prod(r-z for z in roots if z!=r) for e in roots[:2])
        add(pair(a,b,p))
    card={0:2,2:8}.get(p,4)
    for x in list(range(-100,501))+[F(i,j) for j in (2,3,4,5) for i in range(-12,13)]:
        if len(S)==card:break
        if x in roots:continue
        if not cls(prod(x-r for r in roots),p):add(pair(x,x-roots[1],p))
    assert len(S)==card
    return S
def sel(roots):
    g=(-1,2,3,17,409);G=[prod(v**e for v,e in zip(g,t)) for t in product((0,1),repeat=5)]
    I={p:img(roots,p) for p in (0,2,3,17,409)}
    S={(a,b) for a in G for b in G if all(pair(a,b,p) in I[p] for p in I)}
    return S,I
if __name__=='__main__':
    for roots,target in [([0,6953,-20859],409),([0,62577,-20859],17)]:
        S,I=sel(roots);print(roots,len(S),sorted((a,b) for a,b in S if a==target),{p:sorted(v) for p,v in I.items()})
