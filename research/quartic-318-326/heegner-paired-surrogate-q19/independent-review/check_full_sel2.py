from fractions import Fraction as F
from itertools import product
from math import prod
import json

def cls(t,p):
    assert t
    t=F(t)
    a,b=t.numerator,t.denominator
    if p==0:return (a<0,)
    v=0
    while a%p==0:a//=p;v+=1
    while b%p==0:b//=p;v-=1
    if p==2:return (v%2,a*pow(b,-1,8)%8)
    l=pow(a*pow(b,-1,p)%p,(p-1)//2,p)
    assert l in (1,p-1)
    return (v%2,int(l==p-1))
def square(p):
    return (False,) if p==0 else (0,1) if p==2 else (0,0)

def run(n,ps):
    e=(0,n,-3*n)
    S={}
    for p in (0,*ps):
        witness={tuple(square(p) for _ in e):'O'}
        for i,r in enumerate(e):
            a=[r-s for s in e]
            a[i]=prod(t for t in a if t)
            witness[tuple(cls(t,p) for t in a)]=f'T{i}'
        want={0:2,2:8}.get(p,4)
        if p==2:
            cand=[F(j,2**k) for k in (0,2,4) for j in range(-101,102) if j% (2 if k else 100000)]
            cand.extend(F(r+i*2**k) for r in e for k in range(1,7) for i in range(-19,20))
        elif p:
            cand=[F(j) for j in range(-min(3*p,1500),min(3*p,1500))]
            cand.extend(F(r+i*p**k) for r in e for k in range(1,6) for i in range(1,min(p,30)+1))
        else:
            cand=[F(j) for j in (-2*n,2*n)]
        for x in cand:
            if len(witness)==want:break
            z=[x-r for r in e]
            if 0 in z or cls(prod(z),p)!=square(p):continue
            witness.setdefault(tuple(cls(t,p) for t in z),str(x))
        assert len(witness)==want,(p,witness)
        S[p]=witness
    atoms=(-1,*ps)
    bs=[prod(g for i,g in enumerate(atoms) if m>>i&1) for m in range(1<<len(atoms))]
    def sfmul(b,c):
        return bs[bs.index(b)^bs.index(c)]
    def classify(x):
        return tuple(cls(x,p) for p in S)
    cd={c:classify(c) for c in bs}
    classes=[]
    for b,c in product(bs,repeat=2):
        d=sfmul(b,c)
        if all((a,b,c) in T for (_,T),a,b,c in zip(S.items(),cd[b],cd[c],cd[d])):
            classes.append((b,c,d))
    point_count_37=1+sum(1 if (u:=x*(x-n)*(x+3*n))%37==0 else (2 if pow(u%37,18,37)==1 else 0)
                         for x in range(37))
    assert point_count_37 == {323:32,132107:44}[n]
    assert len(classes)==8 and (17,1,17) in classes
    return {'n':n,'point_count_37':point_count_37,'known_support':ps,'local':[{'p':p,'witnesses':[{'kummer':k,'x':x} for k,x in T.items()]} for p,T in S.items()],
            'global_Sel2_triples':classes,'global_Sel2_card':len(classes)}
print(json.dumps([run(323,(2,3,17,19)),run(132107,(2,3,17,19,409))],indent=2))
