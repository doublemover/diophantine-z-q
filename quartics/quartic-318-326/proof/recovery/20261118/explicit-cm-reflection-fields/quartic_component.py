"""Real parts of primitive order-four class characters via splitting in explicit dihedral fields."""
import json,sys,random
from pathlib import Path
from math import gcd
from flint import fmpz
from genus_component import point_at,add,ctx,arb,acb
def rep(F,avoid):
    a,b,c=F
    for h in range(1,40):
        for j in range(h+1):
            for i in (-h,h) if j!=h else range(-h,h+1):
                m=a*i*i+b*i*j+c*j*j
                if gcd(i,j)==gcd(m,avoid)==1 and m>2 and fmpz(m).is_prime():return m
    raise ValueError("no represented prime in search")
def weight(p,b,g,r,s,u):
    if pow(b,(p-1)//2,p)!=1:return 0
    v=int(fmpz((-g)%p).sqrtmod(fmpz(p))); assert (v*v+g)%p==0
    h=pow(u*(r+s*v),(p-1)//2,p)
    k=pow(u*(r-s*v),(p-1)//2,p)
    assert h==k and h in (1,p-1)
    return 1 if h==1 else -1
def Fp_order(p):
    return 1+p+sum(z if z in (0,1) else -1 for i in range(p) for z in [pow(i*(i+1)*(i-3),(p-1)//2,p)])
def verify(d,r,s,t,u,primes):
    ctx.prec=1024
    b=17;g=d//b
    assert b*g==d and r*r+g*s*s==b*t*t and s%8==0 and u*r%4==1
    meta=json.loads((Path(__file__).resolve().parent.parent/'heegner'/('FAST-%d.json'%d)).read_text())
    reducer=[]
    for q in primes:
        assert fmpz(q).is_prime() and 6*d*t*u*s%q!=0 and pow((-d)%q,(q-1)//2,q)==1 and weight(q,b,g,r,s,u)==1
        reducer.append([q,Fp_order(q)])
    p,n=reducer[0];q,k=reducer[1]; assert n&(n-1)==0 and k%p and n%q
    counts={-1:0,0:0,1:0};P=[]
    for F in meta['forms']:
        p=rep(F,6*d*s*t*u)
        assert pow((-d)%p,(p-1)//2,p)==1
        h=weight(p,b,g,r,s,u)
        counts[h]+=1
        if h:
            x,y=point_at(d,F);P.append((x,h*y))
    assert counts[1]==counts[-1]==meta['h']//4 and counts[0]==meta['h']//2
    random.Random(3).shuffle(P)
    while len(P)>1:P=[add(P[j],P[j+1]) if j+1<len(P) else P[j] for j in range(0,len(P),2)]
    x,y=P[0]
    assert not y.contains(0) and x.is_finite() and y.is_finite()
    return dict(d=d,u=u,quartic_polynomial=[1,0,-2*u*r,0,u*u*b*t*t],weights=counts,split_reductions=reducer,X=str(x),Y=str(y))
if __name__=='__main__':
    print(json.dumps([verify(2159,143,8,41,-1,(19,103)),verify(883031,109,8,443,1,(257,43)),verify(883031,109,8,443,409,(59,67))],indent=2))
