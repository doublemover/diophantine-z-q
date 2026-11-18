"""Independent finite evidence by literal enumeration/addition; no CM formulas or CAS."""
from math import isqrt
from collections import Counter
import json

def prime(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def roots2(p):return [r for r in range(p) if r*r%p==2]
def add(P,Q,p,d):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u and (v+y)%p==0:return None
    t=((v-y)*pow(u-x,-1,p) if x!=u else (3*x*x-d*d)*pow(2*y,-1,p))%p
    z=(t*t-x-u)%p;return z,(t*(x-z)-y)%p
def data(p):
    ss={a*a%p for a in range(p)}; passing=pow(2,(p-1)//4,p)==(1 if p%16==1 else p-1)
    out=[]
    for r in roots2(p):
        d=(3-r)%p;T=((1+r)%p,2*r%p);points=[None]
        ys={}
        for y in range(p):ys.setdefault(y*y%p,[]).append(y)
        for x in range(p):
            for y in ys.get((x**3-d*d*x)%p,[]):points.append((x,y))
        doubles={add(P,P,p,d) for P in points}; torsion=[(x,0) for x in (0,d,-d%p)]
        nt=sum(v in doubles for v in torsion)
        assert nt==(3 if d in ss else 0)
        assert (len(points)%16==0 if d in ss else len(points)%8==4)
        assert (T in doubles)==passing==((1+r)%p in ss)
        P=T;order=1
        while P is not None:order+=1;P=add(P,T,p,d);assert order<=len(points)
        assert len(points)%order==0
        if d not in ss:assert (order%2==1)==passing
        if not passing:assert order%(4 if d in ss else 2)==0
        out.append([r,d in ss,order,len(points)])
    if 7 not in ss:
        assert sum(not z[1] for z in out)==1
        assert any(z[2]%2==1 for z in out)==passing
    return passing,7 in ss,out
if __name__=='__main__':
    counts=Counter();examples={}
    for p in range(17,4000,8):
        if not prime(p):continue
        ok,s7,rows=data(p);nodd=sum(z[2]%2 for z in rows)
        counts['primes']+=1;counts['signed_curves']+=len(rows)
        if not s7:
            counts['mixed7']+=1;counts['mixed7_pass']+=int(ok);counts['mixed7_fail']+=int(not ok)
            label=(str(p%16),'pass' if ok else 'fail',str(nodd)+'-odd')
            examples.setdefault('/'.join(label),dict(p=p,sides=rows))
        if s7 and ok and not nodd:examples.setdefault('pass-but-both-even-outside-mixed7',dict(p=p,sides=rows))
    assert 'pass-but-both-even-outside-mixed7' in examples
    assert all(('1/pass/'+v in examples and '9/pass/'+v in examples) for v in ['1-odd','2-odd'])
    print(json.dumps(dict(counts=counts,examples=examples),indent=2))
