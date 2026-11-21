import json
from math import isqrt
from random import Random

def rank(rows, n):
    rows = rows[:]
    i = 0
    for j in range(n):
        q = next((q for q in range(i,len(rows)) if rows[q]>>j&1),None)
        if q is None:
            continue
        rows[i],rows[q]=rows[q],rows[i]
        for k in range(len(rows)):
            if k!=i and rows[k]>>j&1:
                rows[k]^=rows[i]
        i+=1
    return i

# Test the Schur pivot without assuming symmetric row/column.
def append(D, x, y):
    n=len(D)
    choices=[[D[i]|((x>>i&1)<<n) for i in range(n)]+[y|(b<<n)] for b in (0,1)]
    good=[(b,rows) for b,rows in enumerate(choices) if rank(rows,n+1)==n+1]
    assert len(good)==1
    return good[0]

rng=Random(318326)
cores={"plus":[1921,128,292,512,48,20,1024,3,5,9,65],
       "minus":[897,254,346,638,78,106,126,3,5,9]}
report={}
for phase,C in cores.items():
    assert rank(C,len(C))==len(C)
    flips=0
    leaves=0
    for _ in range(96):
        n=len(C)
        x,y=rng.randrange(1<<n),rng.randrange(1<<n)
        # Same r pivot; distinct initial theta row sums of equal parity need not be zero.
        parity=rng.randrange(2)
        auto=[parity,parity]
        bit,Cr=append(C,x,y)
        assert bit^auto[0]==bit^auto[1]
        flips+=bit^auto[0]
        for base in (C,Cr):
            a,b=base[:],base[:]
            for direction,d in enumerate([a,b]):
                m=rng.randrange(5)
                for _ in range(m):
                    _,nextD=append(d,rng.randrange(1<<len(d)),rng.randrange(1<<len(d)))
                    d[:]=nextD
                    leaves+=1
                assert rank(d,len(d))==len(d)
    report[phase]={"old_rank":len(C),"common_repair_one_bits":flips,"appended_side_pivots":leaves}

def prime(n):
    return n>1 and all(n%p for p in range(2,isqrt(n)+1))
def leg(x,p):
    r=pow(x%p,(p-1)//2,p)
    assert r in (1,p-1)
    return 1 if r==1 else -1
p,q,u,v,r=17,73,7,31,63823
beta=p*q
assert all(prime(t) for t in (p,q,u,v,r)) and u*v%24==1
assert (r*u-1)%(24*beta)==0 and r*v%24==1
assert [leg(u*v,t) for t in (p,q)]==[1,1]
assert [leg(beta,t) for t in (u,v,r)]==[1,1,1]
assert [leg(r,t) for t in (u,v)]==[1,1]
assert [leg(t,r) for t in (u,v)]==[-1,-1]
print(json.dumps({"scope":"Schur and reciprocity fixtures, not a numeric original detector",
                 "schur":report,"fix":{"beta":beta,"u":u,"v":v,"r":r,"theta_over_r":leg(u*v,r),
                 "r_over_side_primes":[leg(r,t) for t in (u,v)],"side_primes_over_r":[leg(t,r) for t in (u,v)]}},
                 indent=2,sort_keys=True))
