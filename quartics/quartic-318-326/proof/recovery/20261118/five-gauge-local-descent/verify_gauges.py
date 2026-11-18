"""Exhaust all group arguments in small non-split/split/nontrivial-action controls.
These examples neither certify the general theorem nor run Lean."""
from itertools import product
from random import Random
import json

def run(name,G,H,Q,mul,inv,q,sec,p,act,base):
    rng=Random(314159); tup=lambda n:list(product(G,repeat=n))
    e=G[0]; assert all(mul(e,x)==x==mul(x,e) for x in G)
    hs=lambda x:mul(inv(sec[q(x)]),x)
    assert all(hs(x) in H and mul(sec[q(x)],hs(x))==x for x in G)
    tau=lambda g,a:mul(mul(inv(g),a),g)
    def d2(B,x,y,z): return (act(x,B[y,z])-B[mul(x,y),z]+B[x,mul(y,z)]-B[x,y])%p
    def d3(w,x,y,z,t): return (act(x,w[y,z,t])-w[mul(x,y),z,t]+w[x,mul(y,z),t]-w[x,y,mul(z,t)]+w[x,y,z])%p
    def d1(f,a,b): return (act(a,f[b])-f[mul(a,b)]+f[a])%p
    def closed(w): assert all(d3(w,*s)==0 for s in tup(4))
    def slant(w,g,a,b):return (w[g,tau(g,a),tau(g,b)]-w[a,g,tau(g,b)]+w[a,b,g])%p
    def sub(w,B):
        t={s:(w[s]-d2(B,*s))%p for s in tup(3)}; closed(t); return t
    def primitive(v):
        for row in product(range(p),repeat=len(H)):
            f=dict(zip(H,row))
            if all(d1(f,a,b)==v[a,b] for a,b in product(H,repeat=2)): return f
        raise AssertionError('missing mixed boundary')
    # Start with an inflated quotient class plus an intentionally non-normalized coboundary.
    z={s:(0 if all(a in H for a in s) else rng.randrange(p)) for s in tup(2)}
    w={s:(base(*map(q,s))+d2(z,*s))%p for s in tup(3)}
    closed(w); assert all(not w[s] for s in product(H,repeat=3))
    d={g:primitive({(a,b):slant(w,g,a,b) for a,b in product(H,repeat=2)}) for g in G}
    U={(x,y):(-w[sec[q(x)],hs(x),y])%p if x not in H and y in H else 0 for x,y in tup(2)}
    w1=sub(w,U);assert all(not w1[x,a,b] for x in G for a,b in product(H,repeat=2))
    V={(x,y):w1[x,sec[q(y)],hs(y)] if y not in H else 0 for x,y in tup(2)}
    w2=sub(w1,V);assert all(not w2[x,y,a] for x,y in tup(2) for a in H)
    B={s:(U[s]+V[s])%p for s in tup(2)}
    f={}
    for r in Q:
        g=sec[r]
        for a in H: f[r,a]=(d[g][a]+B[g,tau(g,a)]-B[a,g])%p if r!=q(e) else 0
    W={(x,y):f[q(y),x] if x in H else 0 for x,y in tup(2)}
    w3=sub(w2,W);assert all(not w3[a,b,x] for x in G for a,b in product(H,repeat=2))
    X={(x,y):(-w3[sec[q(x)],hs(x),y])%p if x not in H else 0 for x,y in tup(2)}
    w4=sub(w3,X);assert all(not w4[x,y,z] for x,y,z in tup(3) if y in H or z in H)
    v={}
    for r,t in product(Q,repeat=2):
        v[r,t]=next(c for c in range(p) if all((act(a,c)-c)%p==w4[a,sec[r],sec[t]] for a in H))
    Y={(x,y):v[q(x),q(y)] for x,y in tup(2)}
    w5=sub(w4,Y);assert all(not w5[s] for s in tup(3) if any(a in H for a in s))
    assert all(w5[x,y,z]==w5[sec[q(x)],sec[q(y)],sec[q(z)]] for x,y,z in tup(3))
    assert all(act(a,w5[s])%p==w5[s] for a in H for s in tup(3))
    total={s:sum(T[s] for T in (U,V,W,X,Y))%p for s in tup(2)}
    assert all((w5[s]+d2(total,*s)-w[s])%p==0 for s in tup(3))
    nonzero=sum(bool(w5[sec[r],sec[t],sec[l]]) for r,t,l in product(Q,repeat=3))
    # With F2 trivial, Q=C2, any normalized boundary on (1,1,1) is zero.
    # Even allowing non-normalized primitives, requiring all 8 inputs rules them out.
    if name=='S3':
        for row in product(range(p),repeat=4):
            P=dict(zip(product(Q,repeat=2),row))
            assert any((P[b,c]-P[(a+b)%2,c]+P[a,(b+c)%2]-P[a,b])%p!=w5[sec[a],sec[b],sec[c]] for a,b,c in product(Q,repeat=3))
    return dict(example=name,G=len(G),H=len(H),module_modulus=p,quadruples=len(G)**4,descended_nonzero_values=nonzero)
def dihedral(n):
    G=list(product(range(n),range(2)))
    mul=lambda x,y:((x[0]+(-1)**x[1]*y[0])%n,(x[1]+y[1])%2)
    inv=lambda x:((-(-1)**x[1]*x[0])%n,x[1])
    return G,[(x,0) for x in range(n)],[0,1],mul,inv,lambda x:x[1],{0:(0,0),1:(1,1)}
out=[run('S3',*dihedral(3),2,lambda x,a:a,lambda a,b,c:a*b*c),
    run('D8',*dihedral(4),5,lambda x,a:(-1)**(x[0]+x[1])*a%5,lambda *s:0),
    run('C4 nonsplit',list(range(4)),[0,2],[0,1],lambda x,y:(x+y)%4,lambda x:-x%4,lambda x:x%2,{0:0,1:3},5,lambda x,a:(2**x*a)%5,lambda *s:0)]
print(json.dumps(out,indent=2))
