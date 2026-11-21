#!/usr/bin/env python3
"""Verify all potentially nonsplit collision primes in the actual XVI anchor."""
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path
import sys

def read_pin(path, digest):
    raw = Path(path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest
    return json.loads(raw)

data = read_pin(sys.argv[1], '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
L = int(data['simultaneous_h_modulus'])
J = int(data['literal_scalar_J'])
s = 1 + 6**15 * 3**65536 * J
bits = bin(2*(s-2))[2:]
assert J > 0

# Each listed prime is certified by trial division, and division to 1
# guards completeness. This is only factoring the small finite CRT anchor.
P = [2,3,5,7,11,13,17,19,23,29,31,37,41,47,53,61,73,89,97,101,131,
     149,181,193,233,257,293,337,349,389,397,509,1069,1231,2657,3533,5861,6029,
     6329,6551,8053,21737,27277,42829,51479,54949,69929,118901,144073,351749,
     415721,575921,700789,834149,909529,923129,957953,1041427,1497281,2453441,
     2470991,2664341,3162001,3641809,4247281,4818481,9807649,16688017,16782959,
     17590513,52056721,53279089,86221721,95810641,172237889,344853841,583021393,
     1476960817]
assert P == sorted(set(P))
factors = []
for p in P:
    assert all(p % a for a in range(2, isqrt(p)+1))
    assert L % p == 0
    e = 0
    while L % p == 0:
        e += 1
        L //= p
    factors.append([p,e])
assert L == 1 and len(P) == 78

def target(p):
    return p not in {2,7,11,37,2399} and all(pow(a % p,(p-1)//2,p)==p-1 for a in [2399,-814])
pinned = Path(__file__).with_name('ANNIHILATOR-WITNESSES.txt').read_text().splitlines()
w = {}
for row in pinned:
    p,*rest = map(int,row.split(','))
    assert p not in w and len(rest) in [2,4]
    w[p] = list(zip(rest[::2],rest[1::2]))
assert sorted(w) == [p for p in P if target(p)]

def labels(N):
    # Compute exact Lucas division by s−2 before reducing mod N.
    D = s-2
    g = 1
    while (z := gcd(D,N)) != 1:
        D //= z
        g *= z
    M = N*g
    u = s%M
    x,y = 0,1
    for b in bits:
        A = x*(2*y-u*x)%M
        B = (y*y-x*x)%M
        x,y = (A,B) if b=='0' else (B,(u*B-A)%M)
    assert x%g == 0
    return [3723%N,s%N,y%N,(x//g*pow(D,-1,N))%N]

def evaluate(p,r,N):
    one = (1,0)
    zero = (0,0)
    def a(x,y): return tuple((i+j)%p for i,j in zip(x,y))
    def n(x): return tuple(-i%p for i in x)
    def d(x,y): return a(x,n(y))
    def m(x,y): return ((x[0]*y[0]+2*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    def k(x,z): return tuple(t*z%p for t in x)
    def inv(x): return k((x[0],-x[1]),pow((x[0]*x[0]-2*x[1]*x[1])%p,-1,p))
    def sq(x): return m(x,x)
    rho = (0,1) if r == -1 else (r,0)
    D = sq(d((3,0),rho))
    R = (a(one,rho),k(rho,2))
    def on(P):
        if P is not None:
            x,y = P
            assert sq(y) == d(m(sq(x),x),m(D,x))
        return P
    def add(P,Q):
        if P is None: return Q
        if Q is None: return P
        x,y = P
        X,Y = Q
        if x == X:
            if a(y,Y) == zero: return None
            assert y == Y
            slope = m(d(k(sq(x),3),D),inv(k(y,2)))
        else:
            slope = m(d(Y,y),inv(d(X,x)))
        h = d(d(sq(slope),x),X)
        return on((h,d(m(slope,d(x,h)),y)))
    def mul(j,P):
        Q=None
        while j:
            if j&1: Q=add(Q,P)
            P=add(P,P)
            j//=2
        return Q
    on(R)
    assert N > 0 and mul(N,R) is None
    ll = labels(N)
    z = one
    for l in ll:
        Q = mul(l,R)
        if Q is None:
            z = zero
        else:
            x,y = Q
            u = m(k(y,2),inv(a(sq(x),D))) # asserts every affine denominator is a unit
            z = m(z,u)
    return [r,N,ll,list(z)]

out = []
for p,arms in w.items():
    roots = [r for r,N in arms]
    if roots == [-1]:
        assert pow(2,(p-1)//2,p) == p-1
    else:
        assert len(roots)==2 and roots[0] + roots[1] == p
        assert 0 < roots[0] < roots[1] < p and all(r*r%p==2 for r in roots)
    zz = [evaluate(p,r,N) for r,N in arms]
    avg = zz[0][3][0] if roots == [-1] else sum(x[3][0] for x in zz)*pow(2,-1,p)
    eta = (1+avg)%p
    Pmod = (407*eta**2+32*2399)%p
    assert Pmod != 0
    out.append([p,zz,eta,Pmod])
print(json.dumps({'anchor_factorization':factors,
                  'candidates_both_signs_negative':len(out),'noncollision_rows':out},indent=2))
