from itertools import product
from math import prod

def factors(n):
    out=[]
    p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            n//=p
            assert n%p!=0
        p+=1
    return out+([n] if n>1 else [])

def co(x,p):
    v=0
    while x%p==0:
        x//=p
        v^=1
    if p==2:
        r=x%8
        return v,int(r in (3,7)),int(r in (3,5))
    return v,int(pow(x%p,(p-1)//2,p)==p-1)

def pairing(a,b,p):
    if p==2:
        v,e,w=co(a,p); V,E,W=co(b,p)
        return (e*E+v*W+w*V)%2
    v,u=co(a,p); V,U=co(b,p)
    return ((p//2%2)*v*V+v*U+u*V)%2

def count(n):
    assert n%12==11
    fs=factors(n)
    S=[2,3,*fs]; gens=[-1,*S]
    labels=[prod(p for p,b in zip(gens,row) if b) for row in product((0,1),repeat=len(gens))]
    assert all((int(a<0)*int(b<0)+sum(pairing(a,b,p) for p in S))%2==0 for a in gens for b in gens)
    def condition(a,forward):
        if forward and a<0:return False
        for p in S:
            u=co(a,p)
            if p==2:
                if forward and u not in {(0,0,0),(0,0,1)}:return False
                if not forward and u[0]:return False
            elif p==3 or p%3!=1:
                if forward and u!=(0,0):return False
            else:
                assert n%p==0
                if u not in {(0,0),co(-n if forward else n,p)}:return False
        return True
    a=sum(condition(x,True) for x in labels)
    b=sum(condition(x,False) for x in labels)
    k=sum(p%3==2 for p in fs)
    assert a and b==2**(2+k)*a
    return n,a,b,k

controls=[11,23,35,143,299,323,731,7*19*11,11*23*47]
for n in controls:print(count(n))
# At p=7 the wrong positive target unit is not orthogonal to source [n].
assert pairing(7,7,7)==1 and pairing(-7,7,7)==0
