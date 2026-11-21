#!/usr/bin/env python3
"""Check compact Gaussian degree-29 divisibility and two distinct untouched detector incidences."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import json, runpy
root=Path(__file__).resolve().parent.parent
def pin(rel, digest):
    f=root/rel
    assert sha256(f.read_bytes()).hexdigest()==digest
    return f
def run(rel,digest):
    with redirect_stdout(StringIO()):
        return runpy.run_path(str(pin(rel,digest)))
def read(rel,digest):
    return json.loads(pin(rel,digest).read_bytes())

F=run('linked-detector-w37-depth-r1/check_actual_shallow_formal.py',
      '4302feb27fa532f4e713e512a819c88c975a02993782f4ab9b346b590724ed63')['field']
old=read('rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json',
         '5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7')
u1=read('linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json',
        'd6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c')
h0=int(old['h']); L=int(u1['preserved_old_modulus'])
J=int(old['J']); i=6**15*3**65536*J
assert i%h0==0 and L%int(old['h_CRT_step'])==0
assert L%64==h0%64==0
s=1+i; k=2*(s-2); bits=bin(k)[2:]
def lucas2(N):
    # If (x,y)=(U_n,U_(n+1)), the pair for 2n is
    # (x(2y-sx), y^2-x^2); odd follows the exact recurrence.
    x,y=0,1; a=s%N
    for bit in bits:
        T=x*(2*y-a*x)%N
        U=(y*y-x*x)%N
        if bit=='0':x,y=T,U
        else:x,y=U,(a*U-T)%N
    return x,y
def prime_factors(n):
    p=2
    while p*p<=n:
        if n%p==0:
            yield p
            while n%p==0:n//=p
        p+=1
    if n>1:yield n
def labels(N,divs):
    assert all(N%p==0 for p in divs)
    divs=set(divs)
    g=1; D=s-2
    for p in divs:
        while D%p==0:D//=p;g*=p
    assert gcd(D,N)==1
    a,b=lucas2(N*g)
    assert a%g==0
    out=[3723%N,s%N,b%N,((a//g)*pow(D,-1,N))%N]
    _,A,B,C=out
    assert (B*B-A*(A-2)*B*C+(A-2)**2*C*C-1)%N==0
    return out
def crt(a,A,b,B):
    d=gcd(A,B)
    assert (a-b)%d==0
    q=B//d
    r=(a+A*((b-a)//d)*pow(A//d,-1,q))%lcm(A,B) if q>1 else a%A
    assert r%A==a%A and r%B==b%B
    return r,lcm(A,B)
def prime(p):return p>=2 and all(p%k for k in range(2,isqrt(p)+1))
tri=read('linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json',
         'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec')
assert tri['literal_scalar_J']==str(J)
assert int(tri['old_h_preserved_modulus'])==L
six=read('linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json',
         'd8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0')
XII=read('linked-detector-twelve-compatible-incidences-r1/EXACT-TWELVE-INCIDENCES.json',
         'b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744')
assert int(XII['literal_scalar_J'])==J
XIV=read('linked-detector-low-opposite-unhit-r1/EXACT-LOW-OPPOSITE-NEW-CLASS.json',
          '0d8a8a51bc89c1ba66dee18f22eb40ac51b2b681d227be212517915c7f535efc')
h_old,L_old=int(XIV['simultaneous_h_residue']),int(XIV['simultaneous_h_modulus'])
assert int(XIV['literal_scalar_J'])==J and h_old%L==h0%L and L_old%L==0
assert h_old%29==1 and L_old%29==0 and h_old%2==0 and L_old%2==0
rows_old=tri['rows']+six['rows']+XII['rows']+XIV['rows']
assert len(rows_old)==14
D=XIV['numeric_test_d']; assert D==204
r_old,S_old=int(XIV['numeric_test_r']),int(XIV['numeric_r_modulus'])
h,H=h_old,L_old
r,S=r_old,S_old

# Original T0 quotient, over Q(sqrt(2),i), in order 1,rho,i,rho*i.
from fractions import Fraction as Q
def k(a,b=0,c=0,d=0): return tuple(map(Q,(a,b,c,d)))
def pl(u,v): return tuple(x+y for x,y in zip(u,v))
def ng(u): return tuple(-x for x in u)
def sb(u,v): return pl(u,ng(v))
def sc(u,t): return tuple(x*t for x in u)
def ci(u): return (*u[:2],-u[2],-u[3])
def cr(u): return (u[0],-u[1],u[2],-u[3])
def m(u,v):
    a,b,c,d=u; t,s,q,r=v
    return (a*t+2*b*s-c*q-2*d*r,a*s+b*t-c*r-d*q,
            a*q+2*b*r+c*t+2*d*s,a*r+b*q+c*s+d*t)
def sq(x): return m(x,x)
def d(u,v):
    w=m(v,ci(v)); assert w[2:]==(0,0)
    w1=cr(w); n=m(w,w1)
    assert n[1:]==(0,0,0) and n[0]
    return sc(m(m(u,ci(v)),w1),1/n[0])
Aq=k(44,-24); I=k(0,0,1)
P=(k(24,-16),k(-160,116)); IP=ng(P[0]),m(I,P[1])
def on(P): return sq(P[1])==m(P[0],pl(sq(P[0]),Aq))
assert on(P) and on(IP)
def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P; X,Y=Q
    if x==X:
        if y==ng(Y):return None
        assert y==Y
        a=d(pl(sc(sq(x),3),Aq),sc(y,2))
    else:a=d(sb(Y,y),sb(X,x))
    t=sb(sb(sq(a),x),X); o=(t,sb(m(a,sb(x,t)),y)); assert on(o)
    return o
def mul(b,P):
    o=None
    while b:
        if b%2:o=add(o,P)
        P=add(P,P); b//=2
    return o
T=add(mul(5,P),mul(2,IP))
U=add(mul(5,P),mul(2,(IP[0],ng(IP[1]))))
assert U==tuple(ci(a) for a in T) and 5**2+2**2==29
DEN=lcm(*(y.denominator for y in T[0])); DD=isqrt(DEN); assert DD**2==DEN
DDfac=[953,19793,415721,567569,6469193,9807649,18415993,191616641]
assert DD==prod(DDfac) and all(prime(p) and p%8==1 and p%29!=1 for p in DDfac)
A0=[int(a*DEN)for a in T[0]]
assert tuple(Q(x,DEN)for x in A0)==T[0]

R29=[
    (415721,475,436,10923,103693,29),
    (567569,745,112,7458,58,35380),
    (6469193,2132,1387,33934,202249,29),
    (9807649,3057,680,8296152,2453441,29),
    (18415993,3908,1773,4536137,575389,58),
    (191616641,10496,9025,89396354,47908673,58)]
assert [p for p,*_ in R29]==[p for p in DDfac if p>76176]
# p:(designated scale, theta number, chosen root of theta mod p).
selected={415721:(1,4,113400),9807649:(2,3,4592216)}
assert len({z['prime'] for z in rows_old}|set(selected))==16
roots=[(-1,2),(-1,1),(1,2399),(-32,407)]

roster=[]; O=[]
for p,A,B,rho,N,M in R29:
    pp=p*p
    assert A*A+B*B==p and rho*rho%p==2
    zeta=A*pow(B,-1,p)%p; assert zeta*zeta%p==p-1
    # Nonzero homogeneous x-coordinate numerator over p^2: literal CM membership.
    def num_at(r,z):
        a,b,c,d=A0
        return (a+b*r+c*z+d*r*z)%p
    cm=[[num_at(r,z)for z in (zeta,p-zeta)]for r in (rho,p-rho)]
    assert any(x for a in cm for x in a) and DEN%(pp*p)!=0
    arms=[]; mids=[]
    for rx,o in ((rho,N),(p-rho,M)):
        rx2=rx+p*(((2-rx*rx)//p)*pow(2*rx,-1,p)%p)
        assert rx2*rx2%pp==2
        _,point,uc,formal=F(p,rx2)
        fac=tuple(prime_factors(o))
        assert formal(point(o)) and all(not formal(point(o//q))for q in fac)
        mid=None
        if o%2==0:
            mid=point(o//2); assert not formal(mid)
            mid=[mid[0][0]%p,mid[1][0]%p]
            assert mid[1]==0
        mids.append(mid)
        arms.append((rx,rx2,o,fac,point,uc,formal))
    tests=[]
    for n0,m0 in ((0,1),(1,0)):
        Pord=arms[n0][2]; Qord=arms[m0][2]
        Cq=Qord//2 if mids[m0]==[0,0] else Qord
        assert bool(any(cm[m0])) <= (Cq==29)
        Z=Pord//gcd(Pord,2)
        weak=(gcd(Z,Cq)==1 and h_old%gcd(Z,L_old)==0 and (h_old-1)%gcd(Cq,L_old)==0)
        strong=(gcd(Pord*p**3,Qord)==1 and h_old%gcd(Pord*p**3,L_old)==0
                and (h_old-1)%gcd(Qord,L_old)==0 and gcd(p,L_old)==1)
        tests.append({'primary_index':n0,'opposite_order_mod_T0':Cq,'necessary_order_CRT':weak,
                      'full_order_CRT':strong})
    roster.append({'prime':p,'actual_orders':[N,M], 'roots':[rho,p-rho], 'midpoints':mids,
                   'cm_numerators_mod_p':cm,'orientations':tests})
    if p not in selected:continue
    j,i,z0=selected[p]
    assert any(cm[1]) and M==29 and tests[0]['full_order_CRT']
    row=[]
    for rx,rx2,o,fac,point,uc,formal in arms:
        os=point(o)
        assert os!=(0,0) and os[0]%p==os[1]==0
        ls=labels(p*o,(*fac,p))
        us=[uc(point(k))[0]for k in ls]
        assert all(u%p for u in us)
        f=prod(-pow(u,-1,pp)for u in us)%pp
        row.append({'root':rx,'root_p2':rx2,'order':o,'order_prime_divisors':fac,
                    'formal_first_z':os,'label_period':p*o,'literal_labels':ls,
                    'U_values':us,'product_fixedRoots':f})
    a,b=[x['product_fixedRoots']for x in row]
    norm=a*b%pp; scales=[1,((a+b)*pow(2,-1,pp)+norm)%pp,norm]
    assert all(c%p for c in scales)
    theta=[a*pow(b,-1,pp)%pp for a,b in roots]
    roots_p=[x*pow(c*c,-1,p)%p for c in scales for x in theta]
    assert len(set(roots_p))==12 and 0 not in roots_p
    tgt=(theta[i-1]+p)%pp
    assert (z0*z0-tgt)%p==0
    z=(z0+p*((tgt-z0*z0)//p)*pow(2*z0,-1,p))%pp
    assert z*z%pp==tgt
    factor=z*pow(scales[j],-1,pp)%pp
    Ts=[pow(c*factor,2,pp)for c in scales]
    vv=[prod((t-x)%pp for x in [0,*theta])%pp for t in Ts]
    assert Ts[j]==tgt and Ts[j]%p!=1 and vv[j]%p==0 and vv[j]!=0
    assert all(vv[k]%p for k in range(3) if k!=j)
    r,S=crt(r,S,D*factor,pp)
    h,H=crt(h,H,0,N)
    h,H=crt(h,H,1,M)
    h,H=crt(h,H,p**3,p**4)
    assert pow(p,3,7)==6
    O.append({'prime':p,'AB':[A,B],'assigned_scale':j,'assigned_root_index':i,'arms':row,
              'scales_mod_p2':scales,'distinct_nonzero_scaled_roots_mod_p':roots_p,
              'r_over_d_mod_p2':factor,'T_j_mod_p2':Ts,'contact_values_mod_p2':vv})
assert [z['prime'] for z in roster if any(t['necessary_order_CRT'] and t['opposite_order_mod_T0']==29 for t in z['orientations'])]==[415721,6469193,9807649]
assert H%L_old==0 and h%L_old==h_old
assert S%S_old==0 and r%S_old==r_old%S_old
for row in rows_old+O:
    p=row['prime']; N,M=[q['order']for q in row['arms']]
    assert h%(N*p**3)==0 and h%M==1 and h%p**4==p**3
    assert r*pow(D,-1,p*p)%(p*p)==row['r_over_d_mod_p2']
assert gcd(r,D)==1 and r*r>2*D*D
real=run('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
         '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
real['Ball'].precision=49152
real['Ball'].S=1<<real['Ball'].precision
for step in range(40):
    hpass=h+H*step
    ok,Z=real['real_margin'](hpass)
    if ok:break
else:raise ArithmeticError('no passing real center in this control')
X=real['Ball'].S//(2**64)
iv=[Z.lo//X,-((-Z.hi)//X)]; assert 100*min(map(abs,iv))>2**64 and iv[0]*iv[1]>0
print(json.dumps({'literal_scalar_J':str(J),'prior_fourteen_h_residue':str(h_old),
    'prior_fourteen_h_modulus':str(L_old),'gaussian_multiplier':[5,2],
    'x_denominator_sqrt_exact':str(DD),'x_denominator_sqrt_prime_factors':DDfac,
    'x_scaled_numerators':list(map(str,A0)),'exact_order_29_candidate_roster':roster,
    'rows':O,'simultaneous_h_residue':str(h),'simultaneous_h_modulus':str(H),
    'real_passing_step':step,'real_passing_h':str(hpass),'real_norm_interval_div_2pow64':iv,
    'numeric_test_d':D,'numeric_test_r':str(r),'numeric_r_modulus':str(S)},indent=2))
