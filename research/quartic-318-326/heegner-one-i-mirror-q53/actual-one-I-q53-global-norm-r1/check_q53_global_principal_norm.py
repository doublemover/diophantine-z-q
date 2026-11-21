#!/usr/bin/env python3
"""Exact global norm of the purpose-chosen q53 numerator by cyclotomic-split CRT."""
from pathlib import Path
from math import isqrt,prod
import hashlib,json,contextlib,io,runpy,sys
import sympy as s
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ
sys.set_int_max_str_digits(10000)
ROOT=Path(__file__).resolve().parent.parent
def pin(rel,sha):
    p=ROOT/rel
    assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
    return p
j=json.loads(pin('actual-one-I-ordinary-q53-ideal-r1/EXACT-ORDINARY-Q53-IDEAL-AND-PRINCIPAL-CHART.json',
 'f5e25122b2b58fe2d14ab66aa1bc61992a6446df8d3b4603e460129030da3dc2').read_text())
gpoly=j['Z_equals_G_of_B_desc'];d=j['d']
assert j['numerator_extra_scalar']==j['numerator_shift_m_B_coefficient']==0
p=pin('actual-one-I-cyclotomic13-r1/check_point_field13_presentation.py',
      'ba77f4e59b1bc81357e44a93628104d1510fef911cdc5fe247d998ec1f8c2a76')
with contextlib.redirect_stdout(io.StringIO()) as h:
    m=runpy.run_path(str(p))
assert hashlib.sha256(h.getvalue().encode()).hexdigest()=='7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a'
u,F,G,psi,mulY=(m[a] for a in ('u','f','g','psi','mul'))
def red(n,d):
    h=n.gcd(d);return n.exquo(h),d.exquo(h)
xparts=[(s.Poly(u,u),s.Poly(1,u))]
for a in range(2,7):
    D,odd0=mulY(psi(a),psi(a));N,odd1=mulY(psi(a-1),psi(a+1))
    assert not odd0 and not odd1
    xparts.append(red(D*u-N,D))
Bn,Bd=xparts[0]
for N,D in xparts[1:]:Bn,Bd=red(Bn*D+Bd*N,Bd*D)
Bn,Bd=red(Bn,Bd*2)
ypart=[]
for a,(N,D) in enumerate(xparts,1):
    ypart.append(red(N.diff()*D-N*D.diff(), a*D**2))
# Form a common denominator for all y([a]P)/y(P), so the
# exact residue loop needs only one inverse for the Gaussian sum.
lcm=s.Poly(1,u,domain=s.ZZ)
for _,D in ypart:lcm=s.lcm(lcm,D)
Ynum=[list(map(int,(N*lcm.exquo(D)).all_coeffs())) for N,D in ypart]
Yden=list(map(int,lcm.all_coeffs()))
bn=list(map(int,Bn.all_coeffs()));bd=list(map(int,Bd.all_coeffs()))
f=list(map(int,F.all_coeffs()));gg=list(map(int,G.all_coeffs()))
Bmax=48;vmax=1456
c=json.loads(pin('actual-one-I-explicit-line-field-r2/ACTUAL-FIELD-DISCRIMINANTS.json',
 'b9573239c447acd8f6e3d52d412e3041f9a2a19dd50496b2c58ee45afac68e84').read_text())['integral_scaled_line_polynomial_desc']
assert sum(abs(x)*Bmax**(14-i) for i,x in enumerate(c) if i)<Bmax**14
VmaxSq=13*d*vmax*(vmax+13)*(vmax+39)
zmax=12*(1+isqrt(VmaxSq))
gmax=sum(abs(c)*Bmax**(len(gpoly)-1-i) for i,c in enumerate(gpoly))
bound=(zmax+gmax)**168
r=runpy.run_path(str(pin('actual-one-I-principal-relation-r1/check_exact_first_principal.py',
 '5d25635d009e147c47b90a76a759badf33487066630e2da3a2679455404ea638')))
resultant=r['resultant']
def crt_prime(x):
    while True:
        x=int(s.nextprime(x))
        if x%13==1:return x
def norm_mod(p):
    assert p%13==1
    z=next(x for a in range(2,p) if (x:=pow(a,(p-1)//13,p))!=1)
    assert pow(z,13,p)==1 and z!=1
    field=[a*pow(13,-1,p)%p for a in f]
    assert field[0]==1
    def red(a):return g.gf_rem(g.gf_strip([a%p for a in a]),field,p,ZZ)
    def mul(a,b):return g.gf_rem(g.gf_mul(a,b,p,ZZ),field,p,ZZ)
    def add(a,b):return g.gf_add(a,b,p,ZZ)
    def sub(a,b):return g.gf_sub(a,b,p,ZZ)
    def div(a,b):
        inv,_,gcd=g.gf_gcdex(b,field,p,ZZ)
        assert gcd==[1]
        return mul(a,inv)
    B=div(red(bn),red(bd)); Y=[]
    for a,h in enumerate(Ynum,1):
        Y=add(Y,g.gf_mul_ground(red(h),(pow(z,a,p)-pow(z,-a,p))%p,p,ZZ))
    Y=div(Y,red(Yden))
    H=[]
    for c in gpoly:H=add(mul(H,B),[c%p] if c%p else [])
    W2=g.gf_mul_ground(red(gg),pow(13,4,p)*d%p,p,ZZ)
    return resultant(field,sub(mul(H,H),mul(W2,mul(Y,Y))),p)

P=1; n=0; q=2**61; ps=[]
while P<=2*bound:
    q=crt_prime(q); a=norm_mod(q);ps.append(q)
    n+=P*((a-n)*pow(P,-1,q)%q);P*=q
n=(n+P//2)%P-P//2
w=crt_prime(q)
assert n and abs(n)<bound and n%w==norm_mod(w)
N=abs(n); remain=N; sm={}
for p in s.primerange(2,200000):
    e=0
    while remain%p==0:remain//=p;e+=1
    if e:sm[int(p)]=e
assert sm.get(53)==13
assert prod(p**e for p,e in sm.items())*remain==N
print(json.dumps(dict(d=d,prime_norm_test=53**13,norm_signed=n,norm_digits=len(str(N)),
    exact_small_rational_norm_factors=sm,unfactored_cofactor=remain,
    unfactored_cofactor_digits=len(str(remain)),crt_split_primes=ps,verification_split_prime=w,
    crt_bits=P.bit_length(),bound_decimal_digits=len(str(bound))),
    sort_keys=True,indent=2))
