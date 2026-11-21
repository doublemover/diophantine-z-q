#!/usr/bin/env python3
"""Independent norm by tower multiplication determinants and composite-coordinate checks."""
from pathlib import Path
from functools import cache
import json
from sympy import nextprime
import sys
from hashlib import sha256
from math import gcd
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ

def read_pinned(path,pin):
    b=Path(path).read_bytes(); assert sha256(b).hexdigest()==pin
    return json.loads(b)
A=read_pinned(sys.argv[1],'8c7d250975747b55a0b07b0c31566b613fd203eb427e16310c0e344ca337f5d0')
N=read_pinned(sys.argv[2],'0fc655687e1eac9a2ef192445eefcbef7d092c16c8e75e8bd7e29a5dd205e3e3')
d=N['d']; expected=N['exact_signed_norm']
q=2**61; crt=[]; M=1; a0=0
vmax=A['arch_abs_bound_v']; bmax=A['arch_abs_bound_A']//26
bound=((169*bmax)**2+13*d*vmax*(vmax+13)*(vmax+39))**84
while M<=2*bound:
    q=int(nextprime(q)); crt.append(q); M*=q
assert len(crt)==175 and M.bit_length()==N['crt_modulus_bits']
assert int(nextprime(q))==N['extra_prime']
Q=(53,59,73,83,1009,65537,2147483647,N['extra_prime'])
modulus=1
for p in (*Q,*crt):
    def scal(x,z): return tuple(g.gf_mul_ground(list(x),z,p,ZZ))
    F=tuple(int(c//26**k)%p for k,c in enumerate(A['actual_line_polynomial_desc']))
    assert all(c%26**i==0 for i,c in enumerate(A['actual_line_polynomial_desc']))
    def add(a,b): return tuple(g.gf_add(list(a),list(b),p,ZZ))
    def mul(a,b): return tuple(g.gf_rem(g.gf_mul(list(a),list(b),p,ZZ), list(F),p,ZZ))
    co=[]
    for pc in A['relative_monic_x_coeffs_ascending_num_den']:
        u=(); power=(1,)
        for a,b in pc:
            u=add(u,scal(power,a*pow(b,-1,p)%p))
            power=mul(power,(26,0))
        co.append(u)
    P=[*(scal(v,-1) for v in reversed(co)),(1,)]
    def shift(v): return tuple(add(x,mul(v[-1],y)) for x,y in zip(((),*v[:-1]),P))
    # alpha*sigma(alpha) = 169^2 B^2 - 13*d*v*(v-13)*(v+39).
    w=(scal((1,0,0),169**2),(13*d*13*39%p,),(-13*d*26%p,),(-13*d%p,),(),())
    cols=[w]
    for _ in range(5):cols.append(shift(cols[-1]))
    @cache
    def det(mask):
        if not mask:return (1,)
        j=6-mask.bit_count();w=()
        for k,i in enumerate(i for i in range(6) if mask&(1<<i)):
            a=mul(cols[j][i],det(mask^(1<<i)))
            w=add(w,scal(a,-1) if k&1 else a)
        return w
    z=det(63)
    # Determinant of multiplication by z over Fp[B].
    def pad(x): return list(reversed(x))+[0]*(14-len(x))
    c=[]; x=z
    for i in range(14):
        c.append(pad(x));x=mul(x,(1,0))
    M=list(map(list,zip(*c))); D=1
    for i in range(14):
        j=next((j for j in range(i,14) if M[j][i]%p),None)
        if j is None:D=0;break
        if i!=j:M[i],M[j]=M[j],M[i];D=-D
        a=M[i][i]%p;D=D*a%p
        ia=pow(a,-1,p)
        for r in range(i+1,14):
            t=M[r][i]*ia%p
            M[r][i:]=[(x-t*y)%p for x,y in zip(M[r][i:],M[i][i:])]
    assert D%p==expected%p,(p,D%p,expected%p)
    if p in Q: print(p,D%p)
    else:
        a0+=modulus*((D-a0)*pow(modulus,-1,p)%p); modulus*=p
assert modulus.bit_length()==N["crt_modulus_bits"] and (a0+modulus//2)%modulus-modulus//2==expected
assert abs(expected)==(3**29*13**333*5881)*N['remaining_cofactor_unfactored']
assert len(str(abs(expected)))==2768 and len(str(N['remaining_cofactor_unfactored']))==2379
prime=[True]*200000;prime[0]=prime[1]=False
for q in range(2,448):
    if prime[q]:
        prime[q*q::q]=[False]*len(prime[q*q::q])
assert all(N['remaining_cofactor_unfactored']%q for q in range(2,len(prime)) if prime[q])
print('relative degree 6 then degree 14 multiplication determinants: full signed CRT and every small-prime exclusion PASS')

J=read_pinned(sys.argv[3],'7eca9c5a866bde202054ea426b699d45ebc1de671a27b500b611bc1deb19e238')
K=read_pinned(sys.argv[4],'7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a')
f=K['monic_x_root_poly_coefficients']
assert f[0]==1 and K['d']==d==J['same_actual_d']
assert J['unfactored_cofactor_ideals'][0]['N']==N['remaining_cofactor_unfactored']
for e in [J['small5881'],*J['unfactored_cofactor_ideals']]:
    m,v,w,u,b=map(e.__getitem__,['N','v','W','u','B'])
    assert gcd(m,6*13*d)==1 and 13*u%m==v
    def eval_mod(f,x):
        a=0
        for c in f: a=(a*x+c)%m
        return a
    assert eval_mod(f,v)==0
    assert gcd(eval_mod([a*(len(f)-1-i) for i,a in enumerate(f[:-1])],v),m)==1
    assert (w*w-13*d*v*(v-13)*(v+39))%m==0 and gcd(w,m)==1
    t=u; h=0
    for i in range(6):
        h=(h+t)%m
        s=t*(t-1)*(t+3)%m
        a=(3*t*t+4*t-3)%m
        t=(a*a*pow(4*s,-1,m)-2-2*t)%m
    assert t==u and h==2*b%m and w==169*b%m
    print(len(str(m)),u if m==5881 else 'composite root via doublings',w if m==5881 else pow(m,4,53))
assert pow(N['remaining_cofactor_unfactored'],4,53)==13
