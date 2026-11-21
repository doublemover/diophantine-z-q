#!/usr/bin/env python3
"""Exact finite canary; no modular parametrization or CM reductions asserted."""
import json
from math import comb, gcd, isqrt, prod

P = 61
NPRIMES = (2, 3, 5, 7, 11, 37, 2399)
HPRIMES = (11, 37, 2399)
R = prod(HPRIMES)
AUX = 2207
DISC = -R * AUX  # D=1 unselected canary
NS = 2

def isprime(p):
    return p >= 2 and all(p % t for t in range(2, isqrt(p) + 1))


def chi(n, p):
    return (0, 1, -1)[0 if n % p == 0 else 1 if pow(n, (p-1)//2, p) == 1 else 2]


def f_add(x,y):
    return ((x[0] + y[0]) % P,(x[1] + y[1]) % P)


def f_neg(x):
    return ((-x[0]) % P, (-x[1]) % P)


def f_mul(x,y):
    a,b=x; c,d=y
    return ((a*c+NS*b*d) % P, (a*d+b*c) % P)


def f_pow(x,n):
    out=(1,0)
    while n:
        if n&1:
            out=f_mul(out,x)
        x=f_mul(x,x)
        n//=2
    return out


def supersingular_61():
    # Coefficient of x^(p-1) in [x(x-1)(x-lambda)]^((p-1)/2).
    assert chi(NS,P) == -1
    roots=[]
    js=set()
    for a in range(P):
        for b in range(P):
            z=(a,b)
            s=(0,0)
            for i in range((P-1)//2,-1,-1):
                s=f_add(f_mul(s,z),(comb((P-1)//2,i)**2 % P,0))
            if s != (0,0):
                continue
            roots.append(z)
            z1=f_add(z,(-1,0))
            numerator=f_pow(f_add(f_add(f_mul(z,z),f_neg(z)),(1,0)),3)
            denominator=f_mul(f_mul(z,z),f_mul(z1,z1))
            assert denominator != (0,0)
            js.add(f_mul(f_mul((256 % P,0),numerator),f_pow(denominator,P*P-2)))
    assert len(roots)==30 and len(js)==5 and (0,0) not in js and (1728%P,0) not in js
    return sorted(js)


def ell_add(X,Y):
    A=(76768-407)%P; B=(-76768*407)%P
    if X is None: return Y
    if Y is None: return X
    x,y=X; u,v=Y
    if x==u and (y+v)%P==0: return None
    m=((v-y)*pow(u-x,-1,P) if x!=u else (3*x*x+2*A*x+B)*pow(2*y,-1,P))%P
    z=(m*m-A-x-u)%P
    return (z,(m*(x-z)-y)%P)


def ell_mul(n,Q):
    T=None
    while n:
        if n&1: T=ell_add(T,Q)
        Q=ell_add(Q,Q)
        n//=2
    return T


def countell(p):
    return p+1+sum(chi(x*(x+76768)*(x-407),p) for x in range(p))


def divisors(n, primes):
    ds=[1]
    for p in primes:
        if p*p>n: break
        if n%p==0:
            old=ds[:]
            pp=1
            while n%p==0:
                n//=p
                pp*=p
                ds.extend(d*pp for d in old)
    if n>1: ds.extend(d*n for d in ds[:])
    return ds


def forms(d):
    amax=isqrt(abs(d)//3)
    pmax=isqrt((amax*amax+abs(d))//4)
    # Ordinary exact Eratosthenes up to the largest divisor-test bound.
    pr=bytearray(b'\1')*(pmax+1)
    pr[:2]=b'\0\0'
    for p in range(2,isqrt(pmax)+1):
        if pr[p]: pr[p*p::p]=b'\0'*((pmax-p*p)//p+1)
    primes=[i for i in range(2,pmax+1) if pr[i]]
    out=set()
    for b in range(1,amax+1,2):
        m=(b*b-d)//4
        for a in divisors(m,primes):
            if a<b or a>amax or a*a>m: continue
            c=m//a
            assert b*b-4*a*c==d and gcd(gcd(a,b),c)==1
            out.add((a,b,c))
            if a!=b and a!=c: out.add((a,-b,c))
    return out


def reduce_form(a,b,c,d):
    assert b*b-4*a*c==d and a>0
    while True:
        b-=2*a*((b+a-1)//(2*a))
        c=(b*b-d)//(4*a)
        if a>c: a,b,c=c,-b,a
        else: return (a,abs(b) if a==c else b,c)


def times_ramified(Q,p,d):
    # If p|a, necessarily p|b but p does not divide c (d squarefree).
    # Basis rotation (x,y)->(-y,x) is determinant one.
    a,b,c=Q
    if a%p==0:
        assert c%p!=0
        a,b,c=c,-b,a
    # Keep b mod 2a; unique root 0 mod p. Companion discriminant equality
    # gives the composed ideal/form because the two leading norms are coprime.
    r=b+2*a*((-b*pow(2*a,-1,p))%p)
    assert (r*r-d)%(4*a*p)==0
    return reduce_form(a*p,r,(r*r-d)//(4*a*p),d)


def genus(Q):
    a,b,c=Q
    return chi(a if a%AUX else c,AUX)  # Kronecker (-2207/n)=(n/2207), n>0.


def base_canary():
    assert DISC%4==1 and all(isprime(p) for p in (*HPRIMES,AUX))
    Q=forms(DISC)
    unseen=Q.copy(); reps=[]
    while unseen:
        q=unseen.pop()
        orbit={q}
        for p in HPRIMES:
            new={times_ramified(f,p,DISC) for f in orbit}
            assert not (orbit & new) and orbit|new <= Q
            for f in orbit:
                t=times_ramified(f,p,DISC)
                assert times_ramified(t,p,DISC)==f
                assert genus(t)==genus(f)*chi(-AUX,p)
            orbit|=new
        unseen-=orbit
        assert len(orbit)==8 and sum(genus(f) for f in orbit)==0
        reps.append(min(orbit))
    return {'fundamental_discriminant':DISC,'class_number':len(Q),
            'genus_counts':[sum(genus(f)==v for f in Q) for v in (1,-1)],
            'ramified_free_action_order':8,'ramified_quotient':len(reps),
            'ramified_quotient_mod17':len(reps)%17,
            'lex_first_representatives':sorted(reps)[:3]}


def main():
    C=countell(13); C1=countell(61); tr=P+1-C1; C2=C1*(P+1+tr)
    assert [C,C1,C2]==[16,68,3808]
    g=ell_mul(4,(1,23))
    assert g is not None and ell_mul(17,g) is None
    assert ell_mul(224,(1,23))==ell_mul(5,g) # 224=4*56 and 56=5 mod17
    j=supersingular_61()
    ind=prod(q+1 for q in NPRIMES)
    full=len(j)*ind
    fixed_point_exclusions=((11,7),(37,3),(2399,11),(407,5),
                            (26389,3),(88763,5),(976393,3))
    assert {d for d,_ in fixed_point_exclusions} == set(divisors(R,HPRIMES))-{1}
    for d,q in fixed_point_exclusions:
        assert q in NPRIMES and d%q and chi(-d,q)==-1
    assert full//256*256==full
    print(json.dumps({
        'exact_low_model_root_order':[0,-76768,407],
        'level':prod(NPRIMES),
        'ramified_Atkin_Lehner_signs':[chi(-AUX,p) for p in HPRIMES],
        'targets':{'F13':C,'F61':C1,'F61_squared':C2,'trace61':tr,
                   'order17_coordinate_generator':g,
                   'coordinate_224_of_1_23':ell_mul(224,(1,23))},
        'all_supersingular_j_coords':j,
        'number_of_geometric_marked_labels':full,
        'fixed_point_exclusions_d_to_l':fixed_point_exclusions,
        'exact_geometric_H_orbits':full//8,
        'lower_on_full_Atkin_Lehner_Frobenius_orbits':full//256,
        'unselected_exact_low_curve_canary':base_canary()
    },sort_keys=True,indent=2))

if __name__=='__main__': main()
