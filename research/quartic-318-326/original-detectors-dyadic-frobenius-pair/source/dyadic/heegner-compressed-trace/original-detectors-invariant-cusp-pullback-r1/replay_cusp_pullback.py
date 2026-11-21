"""Verify literal fixed polynomials; no search or modular-form package."""
from collections import defaultdict
import json

def proof(K, full, coefficients, target):
    mod=1<<K
    def pol(x):return {i:t%mod for i,t in x.items() if t%mod}
    def C(a):return pol({0:a})
    def add(a,b):return pol({i:a.get(i,0)+b.get(i,0) for i in a.keys()|b.keys()})
    def neg(a):return pol({i:-t for i,t in a.items()})
    def sub(a,b):return add(a,neg(b))
    def mul(a,b):
     out=defaultdict(int)
     for i,x in a.items():
      for j,y in b.items():out[i+j]+=x*y
     return pol(out)
    def sc(a,n):return pol({i:n*x for i,x in a.items()})
    def sh(a,n):return {i+n:t for i,t in a.items()}
    def iv(a):
     d,= [i for i,t in a.items() if t%2]
     q=sh(a,-d)
     b=sub(C(1),q)
     s=C(1);v=s
     for _ in range(1,K):
      v=mul(v,b);s=add(s,v)
     return sh(s,-d)
    def pw(a,i):
     if i<0:return pw(iv(a),-i)
     out=C(1)
     while i:
      if i&1:out=mul(out,a)
      i//=2
      if i:a=mul(a,a)
     return out
    def di(a,b):return mul(a,iv(b))
    def cp(a,b):return sum_(sc(pw(b,i),t) for i,t in a.items())
    def sum_(l):
     res={}
     for a in l:res=add(res,a)
     return res

    s={1:1}
    if full:
        f=lambda x:di(pw(add(x,C(6)),3),pw(sub(x,C(10)),2))
        g=lambda x:di(pw(sub(x,C(6)),3),sub(x,C(10)))
        fj=lambda x:di(sub(pw(x,2),C(36)),sub(x,C(10)))
        u=s
    else:
        f=lambda x:di(mul(pw(x,2),add(x,C(9))),pw(add(x,C(8)),2))
        g=lambda x:di(mul(x,pw(add(x,C(9)),2)),add(x,C(8)))
        fj=lambda x:di(sub(pw(x,2),C(72)),add(x,C(8)))
        u=add(s,C(1))
    E=sub(f(s),s)
    x=s
    for _ in range(K):x=sub(u,cp(E,x))
    assert f(x)==u
    F=g(x) if full else sub(g(x),C(1))
    assert {i:c%2 for i,c in F.items() if c%2}=={2:1}
    J=fj(x); P=cp({i:c for i,c in enumerate(coefficients) if c},J)
    w=sc({i:1 for i in target},mod//2)
    r=sub(P,w); B={}
    for k in range(K):
        assert all(c%(2**k)==0 for c in r.values())
        a={i for i,c in r.items() if (c//(2**k))%2}
        b=set(); odd=set()
        for e in a:
            while e and e%2==0:
                e//=2;b.symmetric_difference_update({e})
            odd.symmetric_difference_update({e})
        assert not odd
        bb={i:1 for i in b}
        B=add(B,sc(bb,2**k))
        r=sub(r,sc(sub(cp(bb,F),bb),2**k))
    assert not r
    assert P==add(sub(cp(B,F),B),w)
    fn=lambda x:sorted([i,a] for i,a in x.items())
    return dict(modulus=mod,polynomial=coefficients,phase=fn(w),coboundary_primitive=fn(B),
                frobenius=fn(F),cusp_coordinate=fn(J))

partial_cs=[507392,416256,540320,688976,666104,297649,678840,603080,0,1040318,911391]
full_cs=[24790720,8290800,10177780,11909401,14213408,26202676,26851175]
print(json.dumps(dict(partial=proof(20,False,partial_cs,[-9,-3]),
 full=proof(25,True,full_cs,[-5]),scope="fixed cusp trace Frobenius identities; no production value"),
 indent=2,sort_keys=True))
