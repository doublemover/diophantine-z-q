import json
from math import isqrt

def pdivisors(n):
    L=[]
    for j in range(2,isqrt(n)+1):
        if n%j==0:
            L.append(j)
            while n%j==0:n//=j
        if n==1:break
    return L+[n] if n>1 else L

def make_c(p):
    def mul(x,y):
        a,b=x;c,d=y
        return ((a*c-b*d)%p,(a*d+b*c)%p)
    def pn(x,n):
        y=(1,0)
        while n:
            if n&1:y=mul(y,x)
            x=mul(x,x);n//=2
        return y
    return mul,pn

out={}
for p in (11,2399):
    mul,pn=make_c(p)
    factors=pdivisors(p*p-1)
    # Independent actual tame generator, not assumed to be author's choice.
    g=next((a,b) for b in range(1,p) for a in range(p)
        if all(pn((a,b),(p*p-1)//d)!=(1,0) for d in factors))
    u=(3057%p,680%p)
    v=mul(u,pn(g,2))
    norms=[(x*x+y*y)%p for x,y in (u,v)]
    signs=[pow(x,(p-1)//2,p) for x in norms]
    counts=[[(x*x+y*y+1+e*2*x)%p for e in (-1,1)] for x,y in (u,v)]
    assert signs[0]==signs[1]
    assert all(pn(z,4)!=(1,0) for z in (u,v))
    assert all(a and b for a,b in counts)
    out[p]={'inert_gen':g,'prime_divisors':factors,'phases':[u,v],'norms':norms,'norm_Euler':signs,'group_counts':counts}

p=415721; factors=pdivisors(p-1)
g=next(i for i in range(2,p) if all(pow(i,(p-1)//j,p)!=1 for j in factors))
u=(2,2); v=(2*g*g%p,2)
assert all(pow(c,4,p)!=1 for a in (u,v) for c in a)
norms=[(a*b)%p for a,b in (u,v)]
assert [pow(n,(p-1)//2,p) for n in norms]==[1,1]
counts=[[((x+e)*(y+e))%p for e in (-1,1)] for x,y in (u,v)]
assert all(a and b for a,b in counts)
out[p]={'split_gen':g,'prime_divisors':factors,'phases':[u,v],'norms':norms,'norm_Euler':[1,1],'group_counts':counts}
print(json.dumps(out,indent=2))
