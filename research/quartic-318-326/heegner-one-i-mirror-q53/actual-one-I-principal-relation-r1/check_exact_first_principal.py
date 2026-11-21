#!/usr/bin/env python3
"""Exact norm and first λ-divisor coordinate for W - 169 B on the actual twist."""
from pathlib import Path
import hashlib,json,math,sys
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ

H=Path(__file__).resolve().parent
def donor(rel,pin):
    src=(H.parent/rel).read_bytes()
    assert hashlib.sha256(src).hexdigest()==pin
    return json.loads(src)
j=donor('actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json',
        '7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a')
z=donor('actual-one-I-explicit-line-field-r2/ACTUAL-DEGREE14-LINE-FIELD.json',
        '8c7d250975747b55a0b07b0c31566b613fd203eb427e16310c0e344ca337f5d0')
f=j['x_root_poly_coefficients'];d=j['d']
assert z['d']==d
vmax=z['arch_abs_bound_v']; bmax=z['arch_abs_bound_A']//26
assert (vmax,bmax)==(1456,336)
bound=((169*bmax)**2+13*d*vmax*(vmax+13)*(vmax+39))**84

def resultant(a,b,p):
    if not b:return 0
    z=1
    while len(b)>1:
        m=len(a)-1;n=len(b)-1
        assert m>=n
        r=g.gf_rem(a,b,p,ZZ)
        if not r:return 0
        k=len(r)-1
        z=z*(-1 if m*n%2 else 1)*pow(int(b[0]),m-k,p)%p
        a,b=b,r
    return z*pow(int(b[0]),len(a)-1,p)%p

def certificate_mod(p):
    c=[a*pow(13,-1,p)%p for a in f]
    assert c[0]==1
    def mul(a,b):return g.gf_rem(g.gf_mul(a,b,p,ZZ),c,p,ZZ)
    def add(a,b):return g.gf_add(a,b,p,ZZ)
    def sub(a,b):return g.gf_sub(a,b,p,ZZ)
    def scale(a,k):return g.gf_mul_ground(a,k,p,ZZ)
    G=[1,2,p-3,0];Gp=[3,4,p-3]
    I,_,one=g.gf_gcdex(scale(G,4),c,p,ZZ)
    assert one==[1]
    D=sub(mul(mul(Gp,Gp),I),[2,2])
    S=[];a=[1,0]
    for i in range(6):
        S=add(S,a)
        a=g.gf_compose_mod(D,a,c,p,ZZ)
    assert a==[1,0]
    B=scale(S,pow(2,-1,p))
    w=scale(sub(mul(B,B),scale(G,d%p)),169**2)
    return resultant(c,w,p),len(g.gf_gcd(c,w,p,ZZ))-1

def main():
    # The twelve Tate labels use k=1,...,6 followed by their negatives.
    # Only the positive 1 branch cancels in y-dB, to exact depth 4.
    vals={k:4 if k==1 else 2 for k in range(1,13)}
    row=sum(v*pow(k,-1,13) for k,v in vals.items())*pow(12,-1,13)%13
    assert row==11 and sum(vals.values())==26
    q=2**61;N=0;M=1;count=0
    while M<=2*bound:
        q=int(s.nextprime(q));v,_=certificate_mod(q)
        N+=M*((v-N)*pow(M,-1,q)%q);M*=q;count+=1
    N=(N+M//2)%M-M//2
    extra=int(s.nextprime(q))
    assert abs(N)<=bound and N%extra==certificate_mod(extra)[0] and N!=0
    # Strip small rational primes, store exactly the cofactor we did NOT factor.
    rem=abs(N); small={}
    for q in s.primerange(2,200000):
        e=0
        while rem%q==0:rem//=q;e+=1
        if e:small[str(q)]=e
    assert math.prod(int(p)**e for p,e in small.items())*rem==abs(N)
    assert small.get('3',0)>=26
    support={str(q):certificate_mod(q)[1] for q in (53,59,73,83)}
    assert set(support.values())=={0}
    print(json.dumps(dict(d=d,integral_element='W - 169 B = 169 (y/d - B)',
        lambda_projected_norm3_coefficient=row,nonformal_3_valuations_by_scalars=vals,
        norm_abs_digits=len(str(abs(N))), exact_signed_norm=N, crt_modulus_bits=M.bit_length(),
        crt_prime_count=count,extra_prime=extra,small_prime_search_strict_bound=200000,
        proved_small_prime_factorization=small, remaining_cofactor_unfactored=rem,
        remaining_cofactor_digits=len(str(rem)), no_zero_residue_degree_at_small_free_primes=support),
        sort_keys=True,indent=2))
if __name__=='__main__':main()
