#!/usr/bin/env python3
"""Exact relative Gaussian equation over degree14 and composite divisor test."""
from pathlib import Path
from math import comb,gcd,isqrt,lcm,prod
import contextlib,hashlib,io,json,runpy,sys
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
sys.set_int_max_str_digits(12000)
H=Path(__file__).resolve().parent
def pin(rel,sha):
    p=H.parent/rel
    assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
    return p
src=pin('actual-one-I-q53-global-norm-r1/check_q53_global_principal_norm.py',
 '0e41dc574537761e90684bca6bfee44362a6bdf55f6e9839ca165a99b3ee15f7')
with contextlib.redirect_stdout(io.StringIO()) as h:
    m=runpy.run_path(str(src))
assert hashlib.sha256(h.getvalue().encode()).hexdigest()=='31adfcc272aaf806a8cb3838ff58b7d33f5ab3fc1e94dbfd9ad043b79d445079'
orig=json.loads(h.getvalue())
d=m['d']; f=m['f']; xs=m['gg']; Ynum=m['Ynum']; Yden=m['Yden']; bn=m['bn'];bd=m['bd']
Babs=48;Zabs=m['zmax']
fb=m['c']; G=m['gpoly']
C=orig['unfactored_cofactor']
assert gcd(C,6*d*13)==1 and (C%53,pow(C,4,53))==(21,24)
pnext=m['crt_prime']
# Tr_K(B^i * c_j) with c_j the j-th nonleading coefficient of
# prod_{b=1}^6 (X - Z_b^2).  c_j and B^i are actual algebraic integers.
bs=[14*(Babs**i)*comb(6,j)*(Zabs**(2*j)) for j in range(1,7) for i in range(14)]
def roots_traces(f,n,p=0):
    assert f[0]==1
    D=len(f)-1;t=[D]
    for i in range(1,n+1):
        x=-sum(f[j]*t[i-j] for j in range(1,min(i,D+1)))
        if i<=D:x-=i*f[i]
        t.append(x%p if p else int(x))
    return t
def residue(p):
    z=next(x for a in range(2,p) if (x:=pow(a,(p-1)//13,p))!=1)
    assert pow(z,13,p)==1
    f0=[a*pow(13,-1,p)%p for a in f]
    xtr=roots_traces(f0,83,p)
    def red(a):return g.gf_rem(g.gf_strip([v%p for v in a]),f0,p,ZZ)
    def mul(a,b):return g.gf_rem(g.gf_mul(a,b,p,ZZ),f0,p,ZZ)
    def add(a,b):return g.gf_add(a,b,p,ZZ)
    def sub(a,b):return g.gf_sub(a,b,p,ZZ)
    def scale(a,b):return g.gf_mul_ground(a,b,p,ZZ)
    def inv(b):
        i,_,gg=g.gf_gcdex(b,f0,p,ZZ);assert gg==[1]
        return i
    B=mul(red(bn),inv(red(bd)))
    coef=[[1]]
    den=inv(red(Yden))
    ys=list(map(red,Ynum));W2=scale(red(xs),pow(13,4,p)*d%p)
    for b in range(1,7):
        Y=[]
        for a,y in enumerate(ys,1):Y=add(Y,scale(y,(pow(z,a*b,p)-pow(z,-a*b,p))%p))
        Y=mul(Y,den)
        z2=mul(W2,mul(Y,Y))
        coef=[sub(a,mul(b,z2)) for a,b in zip(coef+[[]],[[]]+coef)]
    assert coef[0]==[1]
    inv6=pow(6,-1,p)
    v=[]
    for m in coef[1:]:
        for i in range(14):
            v.append(sum(c*t for c,t in zip(m[::-1],xtr))*inv6%p)
            m=mul(m,B)
    return v
tr=[0]*84;N=1;q=2**61;primes=[]
while N<=2*max(bs):
    q=pnext(q);r=residue(q);primes.append(q);iv=pow(N,-1,q)
    tr=[a+N*((b-a)*iv%q) for a,b in zip(tr,r)]
    N*=q
tr=[(a+N//2)%N-N//2 for a in tr]
fresh=pnext(q)
assert [x%fresh for x in tr]==residue(fresh)
assert all(abs(a)<=b for a,b in zip(tr,bs))
trace=roots_traces(fb,26)
T=s.Matrix(14,14,lambda i,j:trace[i+j]);Ti=T.inv()
B=s.symbols('B');fbp=s.Poly.from_list(fb,B,domain=s.QQ)
Cs=[s.Poly(1,B,domain=s.QQ)]
for j in range(6):
    u=Ti*s.Matrix(tr[14*j:14*(j+1)])
    Cs.append(s.Poly.from_list(list(u)[::-1],B,domain=s.QQ))
def mul(a,b):return (a*b).rem(fbp)
Gb=s.Poly.from_list(G,B,domain=s.QQ);Gb2=mul(Gb,Gb)
Rb=s.Poly(0,B,domain=s.QQ)
for c in Cs:Rb=mul(Rb,Gb2)+c
assert fbp.resultant(Rb)==orig['norm_signed']
def rat_coeffs(P):return [[int(x.p),int(x.q)] for x in P.all_coeffs()]
D=lcm(*(int(c.q) for P in Cs+[Rb] for c in P.all_coeffs()))
assert gcd(D,C)==1
def raw_mod(a,C):return [int(t.p)*pow(int(t.q),-1,C)%C for t in a.all_coeffs()]
class Pivot(Exception):
    def __init__(self,d):self.d=d
def monic(a,M):
    a=g.gf_strip([int(v)%M for v in a])
    if a:
        d=gcd(a[0],M)
        if d>1:raise Pivot(d)
        a=g.gf_mul_ground(a,pow(a[0],-1,M),M,ZZ)
    return a
def mgcd(a,b,M):
    a=monic(a,M);b=monic(b,M)
    while b:a,b=b,monic(g.gf_rem(a,b,M,ZZ),M)
    return a
def one_piece(M):
    try:
        u=mgcd(fb,raw_mod(Rb,M),M)
    except Pivot as e:
        q=e.d
        while (r:=gcd(M,q*q))!=q:q=r
        if q==M:return [dict(M=M,pivot_found_but_all_support=True)]
        return one_piece(q)+one_piece(M//q)
    if len(u)!=2:return [dict(M=M,gcd_degree=len(u)-1)]
    a=-u[1]%M; b=g.gf_eval(G,a,M,ZZ)
    v=[g.gf_eval(raw_mod(P,M),a,M,ZZ) for P in Cs]
    assert g.gf_eval(fb,a,M,ZZ)==0 and g.gf_eval(v,b*b%M,M,ZZ)==0
    db=g.gf_eval(g.gf_diff(fb,M,ZZ),a,M,ZZ)
    dz=2*b*g.gf_eval(g.gf_diff(v,M,ZZ),b*b%M,M,ZZ)%M
    return [dict(M=M,gcd_degree=1,B=a,Z=b,
       line_derivative_gcd=gcd(db,M),mirror_derivative_gcd=gcd(dz,M))]
boxes=one_piece(C)
assert prod(a['M'] for a in boxes)==C
assert len(boxes)==1 and boxes[0]['gcd_degree']==1
assert boxes[0]['line_derivative_gcd']==boxes[0]['mirror_derivative_gcd']==1
print(json.dumps(dict(d=d,relative_mirror_even_polynomial_coefficients_desc_in_B=[rat_coeffs(P) for P in Cs],
    exact_relative_norm_poly_desc_in_B=rat_coeffs(Rb),source_norm_checked=True,
    crt_split_primes=primes,verification_prime=fresh,relative_coeff_denominator_away_from_C=True,
    unfactored_cofactor_composite_test=boxes,residual_non_13th_power_mod53=[C%53,pow(C,4,53)]),sort_keys=True,indent=2))
