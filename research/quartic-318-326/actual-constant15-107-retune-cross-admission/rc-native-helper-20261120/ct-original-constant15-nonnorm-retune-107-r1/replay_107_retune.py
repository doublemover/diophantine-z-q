"""Exact old-period CRT and direct mod-p^9 literal Kummer check."""
from math import gcd, prod
import contextlib, io, json, sys
from itertools import product
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'joined-work-20261120/rc-linked-scalar-specialization-r1'))
with contextlib.redirect_stdout(io.StringIO()):
    import select_scalar_specialization as C
BASE=Path(__file__).resolve().parent.parent/'ct-original-constant15-clear-crossed-retune-r1/EXACT-RETUNE-CONTROLS.json'
old=json.loads(BASE.read_text())
p=107; q=p*p; m_req=7429
h=C.hc; i=C.shift; assert i%h==0
m=i//h; a=old['T_power2_exponent']; A=old['odd_period_lcm']
assert h==old['h'] and C.vp(i,2)==old['v2_i'] and gcd(A*m,p)==1
assert pow(2,(p-1)//2,p)==p-1
E=C.E(p); assert h%106==0 and E.nsmul(106) is None
assert E.nsmul(53) is not None and E.nsmul(2) is not None
r_0=pow(pow(2,a,A),-1,A)
r_1=m_req*pow(m*pow(2,a,q),-1,q)%q
r=r_0+A*(((r_1-r_0)*pow(A,-1,q))%q)
assert 0<r<A*q
assert (m*pow(2,a,q)*r)%q==m_req
for place,n,_,prior in old['periods_and_index_residues']:
    assert i*pow(2,a,n)*r%n==prior==i%n
W=(1+pow(m_req,4,q)*pow(pow(C.R,29,q),-1,q))%q
c=12*W*pow(1+2448*C.B,-1,q)%q
delta=(1-C.B*c*c)%q
assert (W,c,delta)==(8153,3405,107)
e=2952271997968816765
assert pow(e%p,(p-1)//2,p)==pow(5,(p-1)//2,p)==p-1

# Independent modular projective Kummer check of the literal retuned shift.
# O and P initialise adjacent points. In this field P has even order 106:
# adjacent reductions cannot be opposites (odd multiple) or equal (P≠O).
# At O the formulas are resolved by the fixed unit x(P).
l=9; mod=p**l
def add(x,y):return tuple((a+b)%mod for a,b in zip(x,y))
def sub(x,y):return tuple((a-b)%mod for a,b in zip(x,y))
def mul(x,y):
    a,b=x;c,d=y
    return ((a*c+2*b*d)%mod,(a*d+b*c)%mod)
def sq(x):return mul(x,x)
def scale(x,k):return tuple(a*k%mod for a in x)
def N(x):return (x[0]**2-2*x[1]**2)%mod
def inv(x):return scale((x[0],-x[1]),pow(N(x),-1,mod))
D=(11,-6)
def doub(U):
    X,Z=U
    return sq(add(sq(X),mul(D,sq(Z)))),scale(mul(mul(X,Z),sub(sq(X),mul(D,sq(Z)))),4)
def combine(U,V):
    X,Z=U
    Y,S=V
    return sq(add(mul(X,Y),mul(D,mul(Z,S)))),mul((1,1),sq(sub(mul(X,S),mul(Z,Y))))
def kusq(idx):
    P=((1,0),(0,0))
    Q=((1,1),(1,0))
    for b in bin(idx)[2:]:
        R=combine(P,Q)
        P,Q=(doub(P),R) if b=='0' else (R,doub(Q))
        assert all(any(v%p for x in u for v in x) for u in [P,Q])
    X,Z=P
    assert N(X)%p
    return mul(Z,inv(X))
period=106*p**(l-1)
shift_mod=i*pow(2,a,period)*r%period
u,v=kusq(2*(h%period)),kusq(2*shift_mod)
d=min(C.vp(v,p) for v in u if v)
assert d==2 and all(x%p**d==0 for x in v)
units=[tuple(x//p**d for x in z) for z in (u,v)]
ratio=mul(units[1],inv(units[0]))
assert (ratio[0]%q,ratio[1]%q)==(m_req*m_req%q,0)
nu=N(add((1,0),scale(u,pow(C.R,-1,mod))))
W2=(nu*nu+N(ratio)*pow(pow(C.R,29,mod),-1,mod))%q
assert W2==W
# Full conditional matrices after known 107 plus exactly one further prime.
# D_i = stripped true d-unit bit, including D_107=0 from the exact delta/p.
path=Path(__file__).resolve().parent.parent/'ct-original-scalar-mestre-marked-selmer-r1/EXACT-MARKED-SELMER-ROWS.json'
M0=json.loads(path.read_text())
V=tuple(M0['visible'])+(p,)
D0=tuple(M0['true_d_stripped_bits'])+(0,)
assert pow(C.B%p,(p-1)//2,p)==1 and delta//p==1
def ell(z,p):
    v=pow(z%p,(p-1)//2,p)
    assert v in (1,p-1)
    return int(v==p-1)
rbit=lambda p: int(p%4==3)
t=lambda p: int(p%3==2)
assert 35589230039008870789*p%24==23
L0=[[D0[j] if j==k else ell(q,p) for k,q in enumerate(V)] for j,p in enumerate(V)]
ag=[sum(row)%2 for row in L0]
rev=[ag[j]^rbit(p) for j,p in enumerate(V)] # unseen q ≡ 3 mod 4
L0=[row+[ag[j]] for j,row in enumerate(L0)]+[rev+[sum(rev)%2]]
rr=[rbit(p) for p in V]+[1]
tt=[t(p) for p in V]+[1]
A1=[[v^((tt[j]^rr[j])*rr[k]) for k,v in enumerate(row)] for j,row in enumerate(L0)]
def dot(x,y):return sum(a*b for a,b in zip(x,y))%2
def kernel(M,n):
    return [tuple(v) for v in product((0,1),repeat=n) if not any(dot(row,v) for row in M)]
mask=lambda v:sum(b<<j for j,b in enumerate(v))
phi=kernel(A1,14); psi=kernel(list(zip(*A1)),14)
assert sorted(map(mask,phi))==[0,255,16128,16383]
assert sorted(map(mask,psi))==[0,4709,11674,16383]
# Without the final q assumption, the known 13x13 block still tests all visible
# local necessary rows. Its diagonal uses true d-unit bits, not a row sum.
vis_block=[row[:13] for row in A1[:13]]
vis_psi=kernel(list(zip(*vis_block)),13)
assert sorted(map(mask,vis_psi))==[0,4709]
cand=next(v for v in psi if mask(v)==4709)
e2=prod(q for q,b in zip(V,cand) if b)
assert e2==65029284442765 and e2==5*17*107*733*1489*6551 and not dot(tt,cand)
print(json.dumps(dict(prime=p,index=h,point_order=106,old_odd_crt_modulus=A,
    retune_exponent=a,odd_Q107_crt_multiplier=r,i_over_h_mod_107_squared=m_req,
    shift_modulus=period,shift_index_modulus=shift_mod,W_mod_p2=W,c_mod_p2=c,delta_mod_p2=delta,
    direct_Kummer_quotient_mod_p2=[x%q for x in ratio],valuation_U_h_squared=d,
    quadratic_character_five=-1,quadratic_character_e=-1,conditional_further_residue_mod24=23,
    conditional_phi_masks=sorted(map(mask,phi)),conditional_psi_masks=sorted(map(mask,psi)),
    necessary_visible_psi_masks=sorted(map(mask,vis_psi)),known_opposite_class_e2=e2,
    conditional_unknown_aggregate_bits=ag,conditional_unknown_reverse_bits=rev),indent=2))
