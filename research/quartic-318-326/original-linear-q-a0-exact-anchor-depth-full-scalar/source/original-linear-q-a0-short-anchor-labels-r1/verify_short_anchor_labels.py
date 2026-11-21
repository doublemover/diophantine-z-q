#!/usr/bin/env python3
"""Replay finite rows for the shortened a=0 original tuple. No giant coordinate."""
from hashlib import sha256
from math import isqrt, prod, gcd
from pathlib import Path
from fractions import Fraction
import json

base = Path(__file__).resolve().parent
def pin(name, digest):
    data = (base/name).read_bytes()
    assert sha256(data).hexdigest() == digest
    return json.loads(data)

sd = pin('PINNED-ORIGINAL-A0-SCALAR-AND-LABEL-PREFIX.json',
         '5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7')
qdata = pin('PINNED-ORDER-ONLY-Q.json', '0f7167957a8e10351b0a0cba431ceed48557b84533c5fef7e25261b69f413254')
J = int(sd['J'])
s = 1+6**15*3**65536*J
labels = (3723,s,3723,3723)
assert J > 0 and J.bit_length() == 864
assert all(n % 2 for n in labels) and s.bit_length() == 104775
assert (s-1)%3**65551 == 0 and s != 1
assert sd['guards_mod5'] == [4,1,1,1]

p = qdata['p']
assert p == 3162001 and all(p%d for d in range(2,isqrt(p)+1))
h = int(qdata['h']); L = int(qdata['retained_period']); H = int(sd['h'])
assert (h-H)%L == h%5 == h%64 == 0 and h%p == 2
assert h%789968 == (h-1)%791033 == 0
lo,hi=qdata['real_margin_interval_div_2pow64']
assert lo<hi<0 and -100*hi>2**64
divide = lambda a,b: a*pow(b,-1,p)%p
def group(D):
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P; X,Y=Q
        if x==X:
            if (y+Y)%p==0:return None
            assert y==Y
            z=divide(3*x*x-D,2*y)
        else:
            z=divide(Y-y,X-x)
        r=(z*z-x-X)%p
        out=(r,(z*(x-r)-y)%p)
        assert (out[1]**2-out[0]**3+D*out[0])%p==0
        return out
    def multiple(P,k):
        Q=None
        while k:
            if k&1: Q=add(Q,P)
            k//=2
            if k: P=add(P,P)
        return Q
    return multiple

rows=[]
for arm in qdata['arms']:
    rho = arm['rho']; D=(3-rho)**2%p
    assert rho*rho%p==2
    m=arm['exact_halfpoint_order']
    R=(1+rho,2*rho%p)
    multiple=group(D)
    assert multiple(R,m) is None
    def chart(n):
        x,y=multiple(R,n%m)
        u=divide(2*y,x*x+D)
        v=divide(x**4-6*D*x*x+D*D,(x*x+D)**2)
        assert u*v%p and (v*v+D*u**4-1)%p==0
        return u,v
    u,v=chart(1)
    arg=D*u**4%p
    PG=(1-divide(61*arg,65)+divide(16*arg*arg,195))%p
    QG=(1-divide(7*arg,13))%p
    cs=[chart(n) for n in labels]
    assert [list(a) for a in cs[:2]]==arm['n_label_UV'][:2]
    QJ=[(1+divide(5*(v-1),13))%p for u,v in cs[1:]]
    Z=prod(divide(-1,u) for u,v in cs)%p
    assert PG==arm['PG'] and QG==arm['QG'] and PG*QG%p and all(QJ)
    # The formal input is unchanged at fixed h and R; this is the
    # archived certified q^2 residue, not a fresh precision-lift test.
    f=arm['formal_z_mod_q2']
    assert 0 < f < p*p and f%p==0
    rows.append(dict(rho=rho,old_formal_parameter_mod_q2=f,
        uv=cs,qj_nonfirst=QJ,product=Z))
assert sum(r['rho'] for r in rows)==p
z1,z2=[r['product'] for r in rows]
N=z1*z2%p
scales=[1,(divide(z1+z2,2)+N)%p,N]
assert all(scales) and len({a*a%p for a in scales})==3
assert len({-1,-2,2399,-2*407})==4 and p%2399 and p%407
leading=[divide(1,4*c**12) for c in scales]

# Upper bound for algebraic clearing D, before the independent Q/sieve choice.
# P_abscissa=(57-28sqrt(2))/8 has norm 1681/64, both conjugates >1.
assert 57**2-2*28**2==1681 and (57-8)**2>2*28**2
assert gcd(64,912,1681)==1 and 1681<2**11
# hhat(P)<(11/2+10)/2<8; h(Z)<9*s^2.
assert 24*3723**2+20<s*s
C=2*407*2399
assert C<2**21 and 24<s*s and 55<2**6

print(json.dumps(dict(input=0, labels=['3723','1+6^15*3^65536*J','3723','3723'],
    s_bits=s.bit_length(), translated_3_depth_lower_bound=65551,
    old_real_margin_interval_div_2pow64=[lo,hi], retained_h=str(h),
    actual_guard_residues_mod5=[4,1,4,4], q=p, arms=rows,
    scales_mod_q=scales,pole_depths=[1]*3, b_over_q_mod_q=leading,
    clear_log2_upper_bound='55*s*s < 2^209556; ignores extra Q'),indent=2))
