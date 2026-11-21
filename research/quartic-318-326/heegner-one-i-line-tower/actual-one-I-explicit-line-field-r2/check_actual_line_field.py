#!/usr/bin/env python3
"""Recover the actual degree14 line field and degree6 relative x-equation."""
from pathlib import Path
from math import comb
import hashlib,json
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ

H=Path(__file__).resolve().parent
src=H.parent/'actual-one-I-cyclotomic13-r1'/'EXACT-POINT-FIELD-13.json'
raw=src.read_bytes()
pin='7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a'
assert hashlib.sha256(raw).hexdigest()==pin
j=json.loads(raw);f=j['x_root_poly_coefficients'];fv=j['monic_x_root_poly_coefficients']
n=84
assert len(fv)==n+1 and fv[0]==1 and f[0]==13
assert fv==[f[i]*13**(i-1) if i else 1 for i in range(85)]
# Exact Fujiwara-like bound: |coeff_i| ≤ K^i ⇒ |v| < 2K.
K=1
while any(abs(c)>K**i for i,c in enumerate(fv[1:],1)):K+=1
B=2*K
A=6*B
# Traces a_0,...,a_26 and Tr(A^i b_j), 0<=i<14, 1<=j<=6.
# Each b_j is the signed coefficient of the relative monic x-polynomial.
bounds=[14*A**i for i in range(27)]
bounds += [14*A**i * comb(6,k)*B**k for k in range(1,7) for i in range(14)]

def newton_traces(c,N,mod=0):
    d=len(c)-1
    assert c[0]==1
    T=[d]
    for k in range(1,N+1):
        z=-sum(c[i]*T[k-i] for i in range(1,min(k-1,d)+1))
        if k<=d:z-=k*c[k]
        T.append(z%mod if mod else z)
    return T

def exact_mod(l):
    c=[v*pow(13,-1,l)%l for v in f]
    assert c[0]==1
    def add(a,b):return g.gf_add(a,b,l,ZZ)
    def sub(a,b):return g.gf_sub(a,b,l,ZZ)
    def scalar(a,k):return g.gf_mul_ground(a,k,l,ZZ)
    def mul(a,b):return g.gf_rem(g.gf_mul(a,b,l,ZZ),c,l,ZZ)
    def comp(a,b):return g.gf_compose_mod(a,b,c,l,ZZ)
    assert g.gf_gcd(c,g.gf_diff(c,l,ZZ),l,ZZ)==[1]
    G=[1,2,l-3,0];Gp=[3,4,l-3]
    si,_,h=g.gf_gcdex(scalar(G,4),c,l,ZZ)
    assert h==[1]
    D=sub(mul(mul(Gp,Gp),si),[2,2])
    X=[1,0]; after=X; line=[]
    for _ in range(6):
        line.append(scalar(after,13))
        after=comp(D,after)
    assert after==X and len({tuple(v) for v in line})==6
    S=[]
    poly=[ [1] ] # descending coefficients in relative variable x_monic
    for root in line:
        S=add(S,root)
        poly=[add(a,scalar(mul(b,root),-1))
              for a,b in zip(poly+[[]],[[]]+poly)]
    assert poly[0]==[1] and poly[1]==scalar(S,-1)
    # Trace multiplication in degree84 without last modular reduction:
    # powers of u up to 166 evaluated at all roots; divide by 6 because A,b invariant.
    T=newton_traces(c,166,l)
    def trace(x):
        return sum(a*T[i] for i,a in enumerate(x[::-1])) * pow(6,-1,l)%l
    P=[[1]]
    for _ in range(26):P.append(mul(P[-1],S))
    return [trace(x) for x in P]+[trace(g.gf_mul(x,b,l,ZZ)) for b in poly[1:] for x in P[:14]]

def main():
    p=2**29;M=1;x=[0]*len(bounds);mods=[]
    while M<=2*max(bounds):
        p=int(s.nextprime(p));v=exact_mod(p);mods.append(p)
        inv=pow(M,-1,p)
        x=[a+M*((b-a)*inv%p) for a,b in zip(x,v)]
        M*=p
    assert M>2*max(bounds)
    x=[(a+M//2)%M-M//2 for a in x]
    assert all(abs(a)<=b for a,b in zip(x,bounds))
    p=int(s.nextprime(p))
    assert [a%p for a in x]==exact_mod(p)
    T=x[:27]
    C=[1]
    for i in range(1,15):
        r=-sum(C[j]*T[i-j] for j in range(i))
        assert r%i==0
        C.append(r//i)
    y=s.symbols('A')
    q=s.Poly.from_list(C,y,domain=ZZ)
    assert q.gcd(q.diff()).degree()==0
    assert T==newton_traces(C,26)
    mat=s.Matrix(14,14,lambda i,j:T[i+j])
    assert mat.det()!=0
    rel=[]
    for k in range(6):
        b=s.Matrix(x[27+14*k:27+14*(k+1)])
        col=mat.inv()*b if k==0 else mi*b
        if k==0:
            assert list(col)==[0,-1]+[0]*12
            mi=mat.inv()
        rel.append([[int(a.p),int(a.q)] for a in col])
    assert all(a[1]>0 for poly in rel for a in poly)
    fac=s.factorint(abs(q.discriminant()),limit=2000)
    assert abs(q.discriminant())==s.prod(p**e for p,e in fac.items())
    print(json.dumps(dict(d=j['d'],line_trace_selection='A=sum_{k=0}^5 13 u([2]^kP)',
      arch_abs_bound_v=B,arch_abs_bound_A=A,point_source=pin,crt_primes=mods,
      independent_crt_prime=p,crt_modulus_bits=M.bit_length(),
      actual_line_polynomial_desc=C,relative_monic_x_coeffs_ascending_num_den=rel,
      polynomial_discriminant=int(q.discriminant()),
      polynomial_discriminant_factorization_bounded={str(p):int(e) for p,e in fac.items()}),
     sort_keys=True,indent=2))
if __name__=='__main__':main()
