from fractions import Fraction as Q
from itertools import product
from math import prod,gcd
import random

r=(57,80); B=112; rnd=random.Random(682318)
def norm(z):return z[0]**2+z[1]**2
def star(z):return (z[0],-z[1])
def good(p):
    return [(a,b) for a,b in product(range(p),repeat=2)
            if all(norm((a+d,b))%p for d in (-1,0,1))]
def crt(x,y,m,p):return x+m*((y-x)*pow(m,-1,p)%p)
def lift(ps,vec):
    (a,b),m=r,B
    for (u,v),p in zip(vec,ps):
        a,b,m=crt(a,u,m,p),crt(b,v,m,p),m*p
    return a,b
def ray(z,M):
    a,b=z
    return min((x%M,y%M) for x,y in ((a,b),(-a,-b),(b,-a),(-b,a)))
assert (r[0]%16,r[1]%16)==(9,0) and (r[0]%7,r[1]%7)==(1,3)
assert gcd(norm(r),2*B)==1
ntags=ncrt=nsums=negative=0
for ps in ((),(3,),(5,),(11,),(3,5),(5,11),(3,13)):
    M=B*prod(ps);D=2*M
    degree=2*sum(gcd(norm((a,b)),B)==1 for a,b in product(range(B),repeat=2))*prod((p-1)*(p-(1 if p%4==1 else -1)) for p in ps)//4
    assert degree>0
    local=[good(p) for p in ps]
    bucket={}; seen=set(); neg=set()
    for v in product(*local):
        z=lift(ps,v);normz=norm(z);tag=ray(z,M); opposite=ray(star(z),M)
        assert tag not in seen and opposite not in neg and opposite!=tag
        seen.add(tag);neg.add(opposite)
        residue=normz%D
        assert residue%(2*B)==norm(r)%(2*B)
        assert all((residue-norm(w))%p==0 for w,p in zip(v,ps))
        bucket[residue]=bucket.get(residue,0)+1
        for tv in (residue,residue+M,-residue,0,rnd.randrange(-D,D+1)):
            exact=(tv-normz)%D==0
            separated=(tv-norm(r))%(2*B)==0 and all((tv-norm(w))%p==0 for w,p in zip(v,ps))
            assert exact==separated
            ncrt+=1
        compat_a=(residue-normz)%D==0
        compat_b=(residue+M-normz)%D==0
        assert compat_a and not compat_b
        negative+=1
        ntags+=1
    assert not seen.intersection(neg)
    for tv in bucket:
        safe_sizes=[sum((tv-norm(w))%p==0 for w in gp) for gp,p in zip(local,ps)]
        assert bucket[tv]==prod(safe_sizes)
        U=sum(gcd(norm((a,b)),B)==1 for a,b in product(range(B),repeat=2))
        normalized=Q(8*B,U)*prod(Q(p,p-1)*Q(k,p-(1 if p%4==1 else -1))
                                        for k,p in zip(safe_sizes,ps))
        assert Q(2*D,degree)*bucket[tv]==normalized
        nsums+=1
print(f'{ntags} injective two-element tags; {ncrt} exact split CRT tests; {negative} dyadic doubled-conductor failures detected; {nsums} class sum/degree identities')
