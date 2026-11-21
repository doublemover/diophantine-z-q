"""Replay the compact 2-adic retuning, plus tiny integral Kummer controls."""
import contextlib
import io
import json
from math import lcm, prod
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'joined-work-20261120/rc-linked-scalar-specialization-r1'))
with contextlib.redirect_stdout(io.StringIO()):
    import select_scalar_specialization as C0

h, i = C0.hc, C0.shift
assert h == 473592745039516333133760 and C0.vp(i, 2) == 22
fixed = [
    (7, 196), (181, 32724), (1346909, 1814161575200),
    (70850399941, 5019779171659796018964),
    (6551, 6551*lcm(1638, 364)), (2470991, 2470991*lcm(51479, 308874)),
    (16782959, 16782959*lcm(2097870, 699290)),
]
for p, order, w in [(181, 32724, 146), (1346909, 1814161575200, 429536),
                    (70850399941, 5019779171659796018964, 66349154550)]:
    E = C0.E(p)
    assert E.nsmul(order) is None and pow(2, (p-1)//2, p) == p-1
    def U(index):
        x, y = E.nsmul(index % order)
        return E.mul(E.mul(E.Z(2), y), E.inv(E.addf(E.mul(x,x), E.D)))
    u, v = U(h), U(i)
    N = lambda a: (a[0]*a[0]-2*a[1]*a[1]) % p
    a, b = N(u), N(v)
    R = C0.R % p
    X = (1+pow(a*pow(R,-1,p),2,p)+2*(u[0]**2+2*u[1]**2)*pow(R,-1,p)) % p
    Y = b*pow(a*pow(R,15,p),-1,p) % p
    assert (X*X + R*Y*Y) % p == w
e29 = C0.E(29)
assert e29.nsmul(800) is None and e29.nsmul(h % 800) is None and e29.nsmul(i % 800) is None
assert pow(-C0.R,14,29)==28
for p, s, os in [(6551, 0, (1638,364)),
                 (2470991, 439418, (51479,308874)),
                 (16782959, 8151840, (2097870,699290))]:
    if s == 0:
        s = next(x for x in range(1,p) if (x*x-2) % p == 0)
    assert s*s % p == 2
    for t, o in zip((s,p-s),os):
        E=C0.E(p,t)
        assert E.nsmul(o) is None
        assert all(E.nsmul(o//q) is not None for q in C0.factors(o))
assert C0.E(7,3).nsmul(7) is None and C0.E(7,3).Q is not None
assert C0.E(7,4).nsmul(4) is None and C0.E(7,4).nsmul(2) is not None
assert prod([29,181,1346909,70850399941]) == 1+2448*C0.B
H=12*4**(2*h).bit_length()
B=H+2
odd=lambda n: n//(n&-n)
C = lcm(*[odd(n) for _,n in fixed])
r=pow(pow(2,B,C),-1,C)
assert 0 < r < C
rows=[]
for p,n in fixed:
    assert C0.vp(n,2)<=22
    old=i % n
    new=old * pow(2,B,n) * r % n
    assert new==old
    rows.append([p,n,C0.vp(n,2),old])
D=(11,-6)
mul=lambda a,b:(a[0]*b[0]+2*a[1]*b[1],a[1]*b[0]+a[0]*b[1])
add=lambda a,b:(a[0]+b[0],a[1]+b[1])
sub=lambda a,b:(a[0]-b[0],a[1]-b[1])
sq=lambda a:mul(a,a)
norm=lambda a: abs(a[0])+2*abs(a[1])
def db(P):
    X,Z=P
    return sq(add(sq(X),mul(D,sq(Z)))),mul((4,0),mul(mul(X,Z),sub(sq(X),mul(D,sq(Z)))))
def df(P,Q):
    X,Z=P
    Y,V=Q
    return sq(add(mul(X,Y),mul(D,mul(Z,V)))),mul((1,1),sq(sub(mul(X,V),mul(Z,Y))))
def ladder(i):
    U,V=((1,0),(0,0)),((1,1),(1,0))
    for k,bit in enumerate(bin(i)[2:],1):
        m=max(map(norm,U+V))
        W=df(U,V)
        U,V=(db(U),W) if bit=='0' else (W,db(V))
        assert max(map(norm,U+V)) <= 576*m**4
        assert max(map(norm,U+V)).bit_length() <= 6*4**k
    return U
checks=0
for j in range(1,21):
    X,Z=ladder(j)
    for p,d in [(29,None),(17,6),(31,8),(41,17)]:
        E=C0.E(p,d)
        assert d is None or d*d%p==2
        f=lambda a: tuple(v%p for v in a) if d is None else (a[0]+a[1]*d)%p
        v=E.nsmul(j)
        x,z=f(X),f(Z)
        if v is None:
            assert z==E.Z(0) and x!=E.Z(0)
        else:
            assert z!=E.Z(0) and x==E.mul(v[0],z)
        checks+=1
print(json.dumps(dict(h=h,v2_i=C0.vp(i,2),ladder_bits=(2*h).bit_length(),
    norm_log2_bound=H,T_power2_exponent=B,odd_period_lcm=C,odd_multiplier=r,
    periods_and_index_residues=rows,independent_small_ladder_checks=checks),indent=2))
