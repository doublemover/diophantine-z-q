#!/usr/bin/env python3
"""Local replay on the ACTUAL a=0, (J, Lucas) original prefix."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd, isqrt, lcm
from pathlib import Path
import json
import runpy

base = Path(__file__).resolve().parent.parent
def pinned(name, expected):
    file = base / name
    assert sha256(file.read_bytes()).hexdigest() == expected
    return file
scalar_file = pinned('rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json',
                     '5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7')
singleton_file = pinned('linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json',
                        'd6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c')
formal_file = pinned('linked-detector-w37-depth-r1/check_actual_shallow_formal.py',
                     '4302feb27fa532f4e713e512a819c88c975a02993782f4ab9b346b590724ed63')
real_file = pinned('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
                   '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
sd,old = [json.loads(x.read_bytes()) for x in [scalar_file,singleton_file]]
with redirect_stdout(StringIO()):
    field = runpy.run_path(str(formal_file))['field']
    real = runpy.run_path(str(real_file))

p,a,b = 3162001,1065,1424
assert not any(p%d == 0 for d in range(2,isqrt(p)+1))
assert p == a*a+b*b and (a%16,b%16,a%7,b%7,p%408)==(9,0,1,3,1)
m_minus,m_plus = [((a+e)**2+b*b)//4 for e in [-1,1]]
assert [m_minus,m_plus]==[789968,791033]
L,H = map(int,[old['preserved_old_modulus'],sd['h']])
assert (gcd(L,m_minus),gcd(L,m_plus),gcd(m_minus,m_plus),gcd(L*m_minus*m_plus,p))==(16,1,1,1)
assert H%64==L%64==0 and H%5==L%5==0

def crt(x,M,y,N):
    d=gcd(M,N)
    assert (y-x)%d==0
    t=(y-x)//d*pow(M//d,-1,N//d)%(N//d) if N>d else 0
    x,M=(x+M*t)%lcm(M,N),lcm(M,N)
    assert x%N==y%N
    return x,M
x,M = H,L
for y,N in [(0,m_minus),(1,m_plus),(2,p)]:
    x,M=crt(x,M,y,N)
assert x>1
for j in range(32):
    h = x+j*M
    ok,ball = real['real_margin'](h)
    if ok:
        break
else:
    raise ArithmeticError("no certified real margin in tested 32 indices")
q64 = real['Ball'].S//2**64
norm64 = [ball.lo//q64,-((-ball.hi)//q64)]
assert norm64[0]*norm64[1]>0 and 100*min(map(abs,norm64))>2**64
assert (h-H)%L==h%m_minus==(h-1)%m_plus==0
assert h%p==2 and h%5==0 and sd['guards_mod5']==[4,1,1,1]

i = 6**15*3**65536*int(sd['J'])
s,k = 1+i,2*(i-1)
def luc_pair(n, m):
    def prod(A,B):
        a,b,c,d=A;e,f,g,h=B
        return ((a*e+b*g)%m,(a*f+b*h)%m,(c*e+d*g)%m,(c*f+d*h)%m)
    A=(s%m,m-1,1,0); B=(1,0,0,1)
    while n:
        if n&1: B=prod(B,A)
        A=prod(A,A)
        n>>=1
    return B[0],B[2]

def mul(x,y):return x*y%p
def div(x,y):return x*pow(y,-1,p)%p
def norm(tup):return tup[0]*tup[1]%p
roots=[]
arms=[]
for row,nq,use in zip(old['arms'],[m_plus,m_minus],[h-1,h]):
    rho,root2,n,fs=[row[k] for k in ['root','root_mod_p2','order','order_factors']]
    assert root2**2%(p*p)==2 and root2%p==rho and nq%n==0
    assert all(not any(l%d==0 for d in range(2,isqrt(l)+1)) for l in fs)
    from math import prod
    assert prod(fs)==n
    _,P,_,formal = field(p,root2)
    assert formal(P(n)) and all(not formal(P(n//l)) for l in set(fs))
    z = P(use%(n*p))
    assert formal(z) and z[1]==0 and z[0]%p==0 and z[0]%(p*p)!=0
    D=(3-rho)**2%p
    def chart(k):
        x,y=P(k%n)
        assert isinstance(x,tuple) and x[1]==y[1]==0
        x,y=x[0]%p,y[0]%p
        den=(x*x+D)%p
        u=div(2*y,den)
        v=div(x**4-6*D*x*x+D*D,den*den)
        assert (v*v+D*u**4-1)%p==0
        return [u,v]
    uk1,uk=luc_pair(k,n)
    ns=[3723%n,s%n,uk1,uk*pow(s-2,-1,n)%n]
    base_chart=chart(1)
    chart_ns=[chart(nj) for nj in ns]
    assert all(u*v%p for u,v in [base_chart,*chart_ns])
    arg=D*base_chart[0]**4%p
    PG=(1-div(61*arg,65)+div(16*arg*arg,195))%p
    QG=(1-div(7*arg,13))%p
    QJs=[(1+div(5*(v-1),13))%p for (_,v) in chart_ns[1:]]
    assert PG*QG%p and all(QJs)
    rr=[div(-1,u) for u,_ in chart_ns]
    roots.append(prod(rr)%p)
    arms.append(dict(rho=rho,exact_halfpoint_order=n,quarter_count=nq,
                     formal_z_mod_q2=z[0], labels_mod_half_order=ns,
                     base_UV=base_chart,n_label_UV=chart_ns,PG=PG,QG=QG,QJ_nonfirst=QJs,root_product=roots[-1]))
assert sum(x['rho'] for x in arms)==p
realprod=div(sum(roots),2)
normprod=norm(roots)
scales=[1,(realprod+normprod)%p,normprod]
assert all(scales)
# q*t ≡1, e.g. t=(q+1)/q, forces F/v and Delta valuations and
# the leading b_j/q units by the exact literal trace-pole formula.
leading_b=[div(1,4*c**12) for c in scales]
print(json.dumps(dict(p=p, gaussian_ray=[a,b], quarter_counts=[m_minus,m_plus],
    retained_period=str(L),retained_h=str(H),base_crt=str(x),crt_period=str(M),
    real_progression_step=j,h=str(h),real_margin_interval_div_2pow64=norm64,
    h_mod_q=h%p,arms=arms,scales_mod_q=scales, qt_mod_q=1,
    trace_fold_valuation_weights=[3,3,3],pole_depths=[1,1,1],b_over_q_mod_q=leading_b),
    indent=2))
