from math import gcd,lcm,prod,isqrt
from random import Random
from itertools import product
from pathlib import Path
import json,sys,importlib.util
from overlap import trim
def pf(n):
    s=set();d=2
    while d*d<=n:
        if n%d==0:
            s.add(d)
            while n%d==0:n//=d
        d+=1
    if n>1:s.add(n)
    return s
def good(m,n,Pi,L,h):
    A=Pi**3*m
    return gcd(A,n)==1 and h%gcd(A,L)==0 and (h-1)%gcd(n,L)==0
def signatures(keys,T,Pi,L,h):
    return tuple((gcd(T[k],Pi)==1,(h-1)%gcd(T[k],L)==0,h%gcd(Pi**3*T[k],L)==0) for k in keys),tuple(gcd(T[k],T[t])>1 for j,k in enumerate(keys) for t in keys[:j])
def cases():
    r=Random(318326);truth=0;nontriv=0
    for q in range(400):
        n={j:r.randrange(1,40) for j in range(r.randrange(2,20))};ks=list(n)
        keys=[r.choice(ks) for _ in range(30)];ni={k:n[k]*r.randrange(1,33) for k in ks}
        P,L,h=r.randrange(1,81),r.randrange(1,81),r.randrange(70)
        T,_,_,_=trim(ni,lambda k,t:t%n[k]==0,P,L,pf)
        assert signatures(keys,T,P,L,h)==signatures(keys,n,P,L,h)
        if T!=n:nontriv+=1
        for _ in range(12):
            s=[r.randrange(2) for k in range(15)]
            def ok(V):
                return good(lcm(*(V[keys[2*j+b]] for j,b in enumerate(s))),lcm(*(V[keys[2*j+1-b]] for j,b in enumerate(s))),P,L,h)
            assert ok(T)==ok(n);truth+=int(ok(T))
    # Exhaustively compare 2^15 orientations in nontrivially satisfiable mixed-key case.
    n={0:3,1:7,2:15,3:14,4:1}; ni={0:3*7*11,1:7*13,2:15*37,3:14*41,4:97}
    keys=[v for i in range(15) for v in [(0,2,4)[i%3],(1,3)[i%2]]]
    T,_,_,_=trim(ni,lambda k,x:x%n[k]==0,1,4,pf)
    ct=0
    for bits in product((0,1),repeat=15):
        def ok(V):return good(lcm(*(V[keys[2*j+b]] for j,b in enumerate(bits))),lcm(*(V[keys[2*j+1-b]] for j,b in enumerate(bits))),1,4,1)
        assert ok(n)==ok(T);ct+=int(ok(T))
    assert ct>0
    # An opaque private composite is never passed to the factor oracle, even when repeated.
    opaque=(2**127-1)*(2**521-1)
    fn=lambda g: pf(g) if g<1000 else (_ for _ in ()).throw(AssertionError("private factored"))
    T,req,_,_=trim({0:3*opaque,1:7,2:97},lambda k,x:x%[3,7,1][k]==0,1,16,fn)
    assert T[0]==3*opaque and not req and T[2]==1
    return dict(random_full_graphs=400,random_direct_CRT_checks=4800,random_with_opaque_excess=nontriv,
                full_exhaustive_assignments=32768,full_exhaustive_successes=ct,private_composite_bits=opaque.bit_length())
def real():
    # Small copied independent input fixture includes enough groups to exercise
    # private and overlapping primes; never use reported exact orders inside trim.
    R=json.loads((Path(__file__).parent/'FIXTURE.json').read_text())
    def multiply(p,A,pt,n):
        def add(P,Q):
            if P is None:return Q
            if Q is None:return P
            x,y=P;u,v=Q
            if x==u and (v+y)%p==0:return None
            m=(v-y)*pow(u-x,-1,p)%p if x!=u else (3*x*x+A)*pow(2*y,-1,p)%p
            z=(m*m-x-u)%p;return z,(m*(x-z)-y)%p
        P=pt;Q=None
        while n:
            if n&1:Q=add(P,Q)
            P=add(P,P);n//=2
        return Q
    ns={};exact={};pt={};pi=prod(R['primes'])
    for j,(p,data) in enumerate(zip(R['primes'],R['data'])):
        for i,(r,N,order) in enumerate(data):
            k=2*j+i;ns[k]=N;exact[k]=order;pt[k]=(p,-(3-r)**2%p,((1+r)%p,2*r%p))
    T,asked,act,calls=trim(ns,lambda k,x:multiply(*pt[k],x) is None,pi,16,pf)
    assert all(T[k]%exact[k]==0 for k in T)
    keys=list(ns);assert signatures(keys,T,pi,16,0)==signatures(keys,exact,pi,16,0)
    success=[]
    def check(V,b):return good(lcm(*(V[2*j+i] for j,i in enumerate(b))),lcm(*(V[2*j+1-i] for j,i in enumerate(b))),pi,16,0)
    for b in product((0,1),repeat=5):
        assert check(T,b)==check(exact,b)
        if check(T,b):success.append(b)
    assert success==[(1,1,0,0,1)]
    return dict(certified_by_kill_tests=10,largest_input_bits=max(ns.values()).bit_length(),largest_factored_gcd=max(asked),
     active_primes=act,scalar_strip_tests=calls,nonminimal_final_multiples=sum(T[k]!=exact[k] for k in T),satisfying_assignments=success)
if __name__=='__main__':print(json.dumps(dict(generic=cases(),linked_prime_row=real()),indent=2))
