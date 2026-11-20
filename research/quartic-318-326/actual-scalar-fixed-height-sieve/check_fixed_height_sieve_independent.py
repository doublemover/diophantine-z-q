#!/usr/bin/env python3
"""Recompute the literal local rows and verify the exact bounded height sieve."""
from fractions import Fraction
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import sys

source = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
material = json.loads((source/'EXACT-SCALAR-SPECIALIZATION.json').read_text())
target = json.loads((source/'FIXED-H-HEIGHT-SIEVE.json').read_text())
R = 4376874610839020
A = 114444*R
beta = 204618888056724185
support = {2,3,5,11,17,163,661,733,1489,1861,13,37,53,131}
def valuation(a,p):
    i=0
    while not a%p:
        a//=p
        i+=1
    return i
assert prod(p**valuation(R,p) for p in support)==R
assert A//17 % beta == 0 and isqrt(A//(17*beta))**2 == A//(17*beta)
h=lcm(64,131,*[o for os in material['orders'].values() for o in os])
B=6**15*3**65536
need=h*prod(p**((15*valuation(R,p)+2)//2) for p in support)
assert h == material['first_passing_h'] == 473592745039516333133760
assert material['J'] == need//gcd(need,B)
shift=B*material['J']

def local(p,t,o):
    # One true local residue field. t=None denotes the inert quadratic basis.
    def val(r,s=0): return ((r+(t or 0)*s)%p, s%p if t is None else 0)
    def add(a,b): return val(a[0]+b[0],a[1]+b[1])
    def sub(a,b): return val(a[0]-b[0],a[1]-b[1])
    def mul(a,b): return val(a[0]*b[0]+2*a[1]*b[1], a[0]*b[1]+a[1]*b[0])
    def div(a,b):
        d=pow((b[0]**2-2*b[1]**2)%p,-1,p)
        return mul(a,val(d*b[0],-d*b[1]))
    D=mul(val(3,-1),val(3,-1))
    G=val(1,1),val(0,2)
    X,Y=G
    z=val(0)
    assert mul(D,D)!=z and mul(Y,Y)==mul(X,sub(mul(X,X),D))

    def plus(P,Q):
        if P is None: return Q
        if Q is None: return P
        x,y=P
        X,Y=Q
        if x==X and add(y,Y)==z: return None
        k=div(sub(Y,y),sub(X,x)) if x!=X else div(sub(mul(val(3),mul(x,x)),D),mul(val(2),y))
        u=sub(sub(mul(k,k),x),X)
        return (u,sub(mul(k,sub(x,u)),y))
    def scale(n):
        Q=None
        P=G
        while n:
            if n&1: Q=plus(Q,P)
            P=plus(P,P)
            n>>=1
        return Q
    assert o>0 and scale(o) is None
    n=o
    for d in range(2,isqrt(o)+1):
        if not n%d:
            assert scale(o//d) is not None
            while not n%d: n//=d
    if n>1: assert scale(o//n) is not None

    def chart(n):
        P=scale(n%o)
        if P is None: return z
        x,y=P
        return div(mul(val(2),y),add(mul(x,x),D))
    return chart(h),chart(shift)

pinned=target['modular_rows']
seen=set()
deltas={}
for row in pinned:
    p=row['prime']
    assert p not in seen and 11<=p<=500 and all(p%d for d in range(2,isqrt(p)+1))
    seen.add(p)
    assert R*(A+1)*119%p != 0
    if p in support:
        # Exactly the support rows already known by formal-group depth.
        assert p in (11,13,37,53,131)
        assert all(h%o==0 for o in material['orders'][str(p)])
        assert h%131==0 and 2*valuation(shift//h,p)>=15*valuation(R,p)+1
        W=1
    else:
        roots=[i for i in range(p) if i*i%p==2]
        assert len(row['orders'])==(2 if roots else 1)
        tests=[local(p,t,o) for t,o in zip(roots or [None],row['orders'])]
        if roots:
            (u1,w1),(u2,w2)=tests
            H=u1[0]*u2[0]%p
            I=w1[0]*w2[0]%p
            f=(u1[0]**2+u2[0]**2)*pow(2,-1,p)%p
        else:
            ((u,v),(w,z)),=tests
            H=(u*u-2*v*v)%p
            I=(w*w-2*z*z)%p
            f=(u*u+2*v*v)%p
        Q=I*pow(H*pow(R,15,p),-1,p)%p
        N=(1+(H*pow(R,-1,p))**2+2*f*pow(R,-1,p))%p
        W=(N*N+R*Q*Q)%p
        assert (H,I)==(row['H'],row['I'])
    b=A*W*W*pow(1+A,-2,p)%p
    delta=(1-b*pow(17,-1,p))%p
    assert row['W']==W and row.get('b',b)==b and row['delta']==delta
    deltas[p]=delta

bound=target['bound']
assert bound==100000 and 2*bound**2==target['initial_signed_nonzero_ratio_rows_before_gcd']
prime_order=target['processed_prime_order']
assert len(prime_order)==len(seen)==41 and set(prime_order)==seen
low=(2<<bound)-2
def repeat(bits,width,count):
    # Independent concatenation by doubling, not geometric-series multiplication.
    acc=0
    while count:
        if count&1:
            acc=(acc<<width)|bits
        bits|=bits<<width
        width*=2
        count>>=1
    return acc
packs=[]
for p in prime_order:
    delta=deltas[p]
    D=(1-delta)%p
    ok={x*x%p for x in range(p)}
    assert 0 in ok
    b0=9*beta%p
    E=beta*(82*D-18)%p
    F=9*beta*delta**2%p
    a2=[a*a%p for a in range(p)]
    a4=[b0*x*x%p for x in a2]
    rows=[]
    widths=[]
    for d2 in a2:
        ys=[a for a in range(p) if (a4[a]+a2[a]*d2*E+F*d2*d2)%p in ok]
        bit=sum(1<<a for a in ys)
        widths.append(len(ys))
        rows.append(repeat(bit,p,bound//p+1)&low)
    # Check every denominator divisible by p gets the correct quartic-only
    # condition, including the (a,d)=(0,0) residue intentionally retained.
    assert rows[0]&(1<<p)
    assert (rows[0]>>1&1) == (b0 in ok)
    packs.append((Fraction(sum(widths),p*p),p,rows))
assert [(w,p) for w,p,_ in packs]==sorted((w,p) for w,p,_ in packs)
hits=[bound**2]+[0]*len(packs)
last={}
for d in range(1,bound+1):
    num=low
    for i,(_,p,table) in enumerate(packs,1):
        num&=table[d%p]
        if not num: break
        hits[i]+=num.bit_count()
        if i>=27:
            remaining=num
            while (b:=remaining&-remaining):
                last.setdefault(i,[]).append((b.bit_length()-1,d))
                remaining-=b
assert hits==target['unsigned_survivor_counts_before_gcd']
assert hits[30]==1 and hits[31]==0 and not target['primitive_positive_survivors']
print(f'{len(seen)} literal local rows; all {bound**2} unsigned pairs; survivors at steps 27-30: {last}; none at 31')
