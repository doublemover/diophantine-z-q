"""Pure-Python exact Kummer check; no CAS, floating arithmetic or elliptic point search."""
from math import prod
from itertools import product
from fractions import Fraction
from functools import cache
import json

@cache
def cl(x,p):
    assert x
    if not p: return int(x<0)
    v=0
    while x%p==0: x//=p;v+=1
    if p==2: return 4*(v%2)+2*(x%8 in (3,5))+(x%4==3)
    return 2*(v%2)+(pow(x%p,(p-1)//2,p)==p-1)

def screen(d,qs):
    roots=[0,d,-3*d]; places=[0]+qs
    def local(p):
        k=1 if not p else 3 if p==2 else 2; V={0}
        def add(x,y):
            h=cl(x,p)+2**k*cl(y,p)
            V.update({i^h for i in V})
        for r in roots:
            vals=[r-e if e!=r else prod(r-f for f in roots if f!=r) for e in roots]
            add(*vals[:2])
        for e,r,u in product(range(5),roots,[1,-1,2,-2,3,-3,5,-5,7,-7,11,-11,13,-13]):
            if len(V)==2**k: break
            x=r+u*(p or 1)**e
            if x not in roots and cl(prod(x-q for q in roots),p)==0: add(x,x-d)
        assert len(V)==2**k
        return k,V
    C={p:local(p) for p in places}
    signed=[prod(q for q,b in zip([-1]+qs,bits) if b) for bits in product(range(2),repeat=1+len(qs))]
    return sorted((a,b) for a,b in product(signed,repeat=2) if
             all(cl(a,p)+2**k*cl(b,p) in V for p,(k,V) in C.items()))

if __name__=='__main__':
    out=[]; pts=[]
    for d,qs,nums in [(323,[2,3,17,19],(23297,85425,29719,2444)),
                      (132107,[2,3,17,19,409],(134500798043,482802274515,176711378011,750654112))]:
        assert d==prod(qs[2:]) and d%12==11
        U,V,W,D=nums;u,v,w=[Fraction(k,D) for k in nums[:3]]
        x=17*u*u;y=17*u*v*w
        assert x-d==v*v and x+3*d==17*w*w and y*y==x*(x-d)*(x+3*d)
        pts.append((u,y))
        points=screen(d,qs)
        assert len(points)==8 and (17,1) in points
        out.append(dict(d=d,uvw_common_denominator=nums,selmer_pairs=points))
    c=Fraction(204,1073); b=c*c; B=17*b; V=B**2*(1-b/17); D=B*Fraction(53,1073)
    assert B==17*c*c and V==409*D*D
    (u,y),(U,Y)=pts; E=323*(c/u)**2;s=U*D/u
    y1=y*(c/u)**3;y2=Y*(c*D/u)**3
    def f(e,x):return x*(x-e)*(x+3*e)
    assert E*s*y1*y2 and y1*y1==f(E,B) and y2*y2==f(E*V,B*s*s)
    print(json.dumps(dict(curves=out,point_pair={k:str(z) for k,z in
          zip(('b','E','s','y1','y2'),(b,E,s,y1,y2))}),indent=2))
