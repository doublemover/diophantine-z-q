"""Exact feasibility using certified multiples and only active-prime factorizations.

keys represent *known identical* generators when reused. Different keys are
also safe for equal generators, possibly less efficient. 'primes_of(G)' must
supply the COMPLETE certified prime support of G; no private G is requested.
"""
from math import gcd
def trim(bounds, kills, Pi, L, primes_of):
    if min(Pi,L)<=0 or not bounds or any(n<=0 for n in bounds.values()):
        raise ValueError("nonempty, positive input required")
    ns=dict(bounds);calls=0
    for k in ns:
        if not kills(k,ns[k]):raise ValueError("not an annihilator")
        if kills(k,1):ns[k]=1
    keys=list(ns);asked=set()
    for j,k in enumerate(keys):
        for B in [Pi,L]+[ns[t] for t in keys[:j]]:
            G=gcd(ns[k],B)
            if G>1:asked.add(G)
    act=set()
    for G in sorted(asked):
        s=set(primes_of(G));remainder=G
        for ell in s:
            if ell<=1 or remainder%ell:raise ValueError("false support")
            while remainder%ell==0:remainder//=ell
        if remainder!=1:raise ValueError("incomplete support")
        # Primality is a contract of primes_of; complete factor multiplication
        # alone is not a proof that each support entry is prime.
        act.update(s)
    T=dict(ns)
    for k in keys:
        for ell in sorted(act):
            while T[k]%ell==0:
                calls+=1
                if not kills(k,T[k]//ell):break
                T[k]//=ell
    return T,sorted(asked),sorted(act),calls
