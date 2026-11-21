"""Literal a=617 h,J, using exact finite annihilators and directed real intervals."""
import ast,hashlib,json,math
from pathlib import Path
from math import gcd,lcm,isqrt,prod
from fractions import Fraction

root=Path(__file__).resolve().parents[3]
donor=root/'joined-work-20261120/rc-linked-scalar-specialization-r1/select_scalar_specialization.py'
raw=donor.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91'
names={'vp','E','Ball','real_u','real_margin'}
nodes=[n for n in ast.parse(raw).body if getattr(n,'name',None) in names]
assert {n.name for n in nodes}==names
ns={'math':math}
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(donor),'exec'),ns)
vp,E,Ball,real_margin=(ns[t] for t in ['vp','E','Ball','real_margin'])

beta=199477972060937362209233596181078921
br=3110779382579465849645476448239049522505521
R=66540735456245258815946020283188225080332
K=7615187928554532399932126345289193231093515409
SUP=(2,3,5,11,13,17,47,59,359,601,429467,31634611,506153777,2839205137)
Rraw_primes=(2,11,359,601,429467,31634611,506153777,2839205137)
assert R==prod(p**vp(R,p) for p in Rraw_primes)
assert br==187*R//4==beta*(11*359)**2 and K==1+2448*br
assert all(all(p%k for k in range(2,isqrt(p)+1)) for p in SUP)

def roots(a,p):
    a%=p
    if not a:return [0]
    if pow(a,(p-1)//2,p)!=1:return []
    s=vp(p-1,2);q=(p-1)>>s
    z=next(i for i in range(2,p) if pow(i,(p-1)//2,p)==p-1)
    c=pow(z,q,p);t=pow(a,q,p);r=pow(a,(q+1)//2,p)
    while t!=1:
        i=next(i for i in range(1,s) if pow(t,1<<i,p)==1)
        b=pow(c,1<<(s-i-1),p)
        r=r*b%p;c=b*b%p;t=t*c%p;s=i
    assert r*r%p==a
    return sorted([r,p-r])

def two_squares(p):
    for r in roots(-1,p):
        a,b=p,r
        while b*b>p:a,b=b,a%b
        y=isqrt(p-b*b)
        if b*b+y*y==p:return (b,y)
    raise AssertionError(p)

def brute_order(e):
    P=e.Q
    m=1
    while P is not None:
        P=e.add(P,e.Q)
        m+=1
        assert m<e.q+1+2*isqrt(e.q)
    return m
def certificate(p,s):
    e=E(p,s)
    if p<=59:
        cand=[brute_order(e)]
    elif s is not None and p%4==3:
        cand=[p+1]
    elif s is not None:
        a,b=two_squares(p)
        cand=sorted({p+1+sign*2*x for sign in [-1,1] for x in [a,b]})
    elif p%4==3:
        cand=[(p-1)**2,p*p+1,(p+1)**2]
    else:raise AssertionError(p)
    n=next(n for n in cand if e.nsmul(n) is None)
    return [s,n]
ann={p:[certificate(p,s) for s in roots(2,p) or [None]] for p in SUP if p!=2}
h0=lcm(64,*(n for ns in ann.values() for _,n in ns))*prod(p**(vp(R,p)//2) for p in SUP if p!=2)
assert all(h0%n==0 for ns in ann.values() for _,n in ns)

# The exact modulo-59 guard uses order 60 and s_lab=1 modulo 60.
assert ann[59]==[[None,60]] and 60 and h0%60==0
e59=E(59)
labels=(3723*1235**2,1,-1,1)
guard=[e59.recip(-2*j)[0] for j in labels]
assert guard==[8,32,32,32]

# First real-margin passing positive multiple in the checked short prefix.
Ball.precision=4096
Ball.S=1<<Ball.precision
scans=[]
for j in range(1,129):
    h=h0*j
    ok,I=real_margin(h)
    sc=1<<64
    lo=I.lo*sc//Ball.S
    hi=-((-I.hi*sc)//Ball.S)
    scans.append([j,lo,hi])
    if ok:
        assert not lo<=0<=hi and 100*min(abs(lo),abs(hi))>sc
        break
else:raise AssertionError('adjust finite prefix instead of claiming a least passing index')
N=65536
E0=6**15*3**N
mpart=prod(p**((15*vp(R,p)+2)//2) for p in SUP)
J=h*mpart
assert all(2*vp(E0*mpart,p)>=15*vp(R,p)+1 for p in SUP)
assert J%60==0 and vp(h,2)>=6 and (br//17)%17==1 and br%8==1 and br%3==2
def d0(p):return (1-br*(12*pow(K,-1,p))**2)%p
assert [d0(p) for p in (5,13,47)]==[2,4,46]
print(json.dumps(dict(a=617,R=R,K=K,raw_beta=br,h=h,J=J,h0=h0,
    h_bitlength=h.bit_length(),J_bitlength=J.bit_length(),
    label_s_minus_one_bitlength=(E0*J).bit_length(),
    literal_anchor="i=6^15*3^65536*J; s_lab=1+i; k=2(s_lab-2)",
    label0=labels[0],guard_prime=59,guard_real_numerators=guard,
    finite_checked_annihilators=ann,precision_bits=Ball.precision,
    interval_exponent=64,margin_short_prefix=scans,
    unit_delta_rows=[[p,d0(p)] for p in (5,13,47)]),sort_keys=True,indent=2))
