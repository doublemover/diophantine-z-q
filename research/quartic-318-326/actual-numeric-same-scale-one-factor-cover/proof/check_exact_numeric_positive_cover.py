#!/usr/bin/env python3
"""Actual numeric b-only cover on retained XVI, finite exact rational point and same h."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd,lcm,isqrt,prod
from pathlib import Path
from fractions import Fraction as F
import json,runpy
root=Path(__file__).resolve().parent.parent
def pin(rel, dig):
    p=root/rel
    assert sha256(p.read_bytes()).hexdigest()==dig
    return p
def read(rel,dig):return json.loads(pin(rel,dig).read_bytes())
def run(rel,dig):
    with redirect_stdout(StringIO()):return runpy.run_path(str(pin(rel,dig)))
XVI=read('linked-detector-gaussian-order29-new-classes-r1/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json',
          '6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
J=int(XVI['literal_scalar_J']); h0,L0=map(int,(XVI['simultaneous_h_residue'],XVI['simultaneous_h_modulus']))
old=[
 ('linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json','a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec'),
 ('linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json','d8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0'),
 ('linked-detector-twelve-compatible-incidences-r1/EXACT-TWELVE-INCIDENCES.json','b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744'),
 ('linked-detector-low-opposite-unhit-r1/EXACT-LOW-OPPOSITE-NEW-CLASS.json','0d8a8a51bc89c1ba66dee18f22eb40ac51b2b681d227be212517915c7f535efc')]
S=[t for f,hsh in old for t in read(f,hsh)['rows']]+XVI['rows']
assert len(S)==16 and len({t['prime'] for t in S})==16
Sprod=prod(t['prime'] for t in S)
F0=run('linked-detector-w37-depth-r1/check_actual_shallow_formal.py',
       '4302feb27fa532f4e713e512a819c88c975a02993782f4ab9b346b590724ed63')['field']
def exponents(n):
    for p in range(2,isqrt(n)+1):
        if n%p:continue
        e=0
        while not n%p:n//=p;e+=1
        yield p,e
    if n>1:yield n,1
def vp(r,p):
    r=F(r)
    if r==0:return 10**8
    a,b=r.numerator,r.denominator;e=0
    while a%p==0:a//=p;e+=1
    while b%p==0:b//=p;e-=1
    return e
def mod(r,m):
    r=F(r);return r.numerator*pow(r.denominator,-1,m)%m
def chi(a,p):return {0:0,1:1,p-1:-1}[pow(a%p,(p-1)//2,p)]
def isprime(p):return p>=2 and all(p%r for r in range(2,isqrt(p)+1))
def sqrtmod(a,p):
    a%=p; assert chi(a,p)==1
    q=p-1; e=0
    while q%2==0:q//=2;e+=1
    z=next(j for j in range(2,p) if chi(j,p)==-1)
    u,t,r=pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
    while t!=1:
        i=next(j for j in range(e) if pow(t,2**j,p)==1)
        z=pow(u,2**(e-i-1),p)
        r=r*z%p;t=t*z*z%p;u=z*z%p;e=i
    assert r*r%p==a
    return r
def rootsmod(a,p,k):
    assert p%2
    a%=p**k;r=sqrtmod(a,p); m=p
    for j in range(1,k):
        r+=m*((a-r*r)//m)*pow(2*r,-1,p)% (p*m)
        r%=p*m;m*=p
    assert r*r%m==a
    return (r,m-r)
def crt(a,A,b,B):
    g=gcd(A,B)
    assert (a-b)%g==0
    P=A*(B//g)
    q=(a+A*((b-a)//g*pow(A//g,-1,B//g)))%P if B>g else a%A
    assert q%A==a%A and q%B==b%B
    return q,P
# Same fixed analytic Lucas index; only compute exact local labels mod p·ord.
i=6**15*3**65536*J
s=1+i; k=2*(s-2); KB=bin(k)[2:]
def labels(N):
    de=s-2; g=1
    for p,_ in exponents(N):
        while not de%p:de//=p;g*=p
    x,y=0,1; M=N*g; Z=s%M
    for bit in KB:
        A=x*(2*y-Z*x)%M;B=(y*y-x*x)%M
        x,y=(A,B) if bit=='0' else (B,(Z*B-A)%M)
    assert x%g==0
    l=(3723%N,s%N,y%N,((x//g)*pow(de,-1,N))%N)
    _,A,B,C=l
    assert (B*B-A*(A-2)*B*C+(A-2)**2*C*C-1)%N==0
    return l

qs=((5268121,765,2164,2108966,1317413,164581),(21191329,177,4600,3018173,1324436,5297921))
p1,p2=qs[0][0],qs[1][0]
b=p1*p2; assert b==111638485322809 and chi(p1,p2)==1
FIX=(2,3,5,7,11,17,37,2399)
assert b%8==1 and all(chi(b,p)==1 for p in FIX if p!=2)
assert chi(b,23)==-1 # exact obstruction to promoting this to full B saturation
theta=F(1,2399)
Q1=F(166124172,2399*3384835); Q2=F(1,2399*3384835)
X,Y,Z=166124172,1,3384835
assert X*X-b*Y*Y==2399*Z*Z and Q1*Q1-b*Q2*Q2==theta
h,H=h0,L0; cells=[]; new=[]
for p,A,C,rr,np,no in qs:
    assert isprime(p) and p>76176 and p%8==1 and gcd(p,L0*Sprod)==1
    assert (chi(p,3),chi(p,5),chi(p,7),chi(p,11),chi(p,37),chi(p,2399))==(1,1,-1,1,-1,1)
    assert A*A+C*C==p and A%2 and not C%2 and rr*rr%p==2
    gs=(p+1-2*A,p+1+2*A)
    assert gcd(gs[0],gs[1])&(gcd(gs[0],gs[1])-1)==0
    assert gcd(prod(gs),Sprod)==1 and gcd(prod(gs),p1*p2//p)==1
    assert no%2 and gcd(np,no)==1
    pp=p*p; ar=[]
    for r,o in ((rr,np),(p-rr,no)):
        r2=r+p*(((2-r*r)//p)*pow(2*r,-1,p)%p)
        order,point,U,formal=F0(p,r2)
        assert order(gs)==o and gcd(p,o)==1
        z=point(o)
        assert formal(z) and z[1]==0 and vp(z[0],p)==1
        ls=labels(p*o); us=[U(point(k))[0] for k in ls]
        assert all(u%p for u in us)
        R=prod(-pow(u,-1,pp) for u in us)%pp
        ar.append(dict(r=r,r_p2=r2,order=o,order_factorization=list(exponents(o)),
                       first_formal_z=z[0],labels=ls,U_p2=us,product=R))
    ap,am=[z['product'] for z in ar]
    cs=[1,((ap+am)*pow(2,-1,pp)+ap*am)%pp,ap*am%pp]
    assert all(c%p for c in cs)
    roots=[0,F(-1,2),-1,theta,F(-32,407)]
    allroots=[mod(rt,p)*pow(c*c,-1,p)%p for c in cs for rt in roots[1:]]
    assert len(set(allroots))==12 and all(allroots)
    Wt=rootsmod(mod(theta,pp)+b,p,2)[0]
    want=Wt*pow(cs[1],-1,pp)%pp
    TT=[pow(c*want,2,pp) for c in cs]
    Fs=[prod(t-mod(r,pp) for r in roots)%pp for t in TT]
    assert TT[1]==(mod(theta,pp)+b)%pp and TT[1]%p!=1
    assert Fs[1]%p==0 and Fs[1]!=0 and Fs[0]%p and Fs[2]%p
    intervals={}
    for e,ed in ((0,np),(1,no),(p**3,p**4)):h,H=crt(h,H,e,ed)
    new.append(dict(p=p,AB=[A,C],arm_counts=gs,arms=ar,c_mod_p2=cs,
             exact_W_target=Wt,w_mod_p2=want,T_rows=TT,F_rows=Fs))
    cells.append((p,Wt))
for row in S:
    p=row['prime'];pp=p*p
    Wt=row['scales_mod_p2'][1]*row['r_over_d_mod_p2']%pp
    assert (Wt*Wt-mod(theta,pp))%p and chi(mod((F(Wt)**2-theta)/b,p),p)==1
    cells.append((p,Wt))
assert len(cells)==18
assert h%L0==h0 and H%L0==0
assert all(h%r['arms'][0]['order']==0 and h%r['arms'][1]['order']==1 and h%r['p']**4==r['p']**3 for r in new)

# Rational parameter of norm-one multiplication of the exact base pair.
def conic(U,V):
    d=2399*Z*(V*V-b*U*U)
    assert d
    return (F(X*(V*V+b*U*U)+2*b*U*V,d),F(V*V+b*U*U+2*X*U*V,d))
def denominator(U,V):return 2399*Z*(V*V-b*U*U)
a,v,M=0,0,1
cong=[]
for p,Wt in cells:
    if p in (p1,p2):
        room=[1,-1]
    else:
        room=rootsmod(mod((F(Wt)**2-theta)/b,p**8),p,8)
    for yy in room:
        u=2399*(yy*Q1-Wt*Q2)
        v1=1+2399*(Wt*Q1-b*yy*Q2)
        if not v1:continue
        uv=u/v1; U,V=uv.numerator,uv.denominator
        W2,Y2=conic(U,V)
        if vp(W2-Wt,p)<2:continue
        if p in (p1,p2) and vp(Y2-yy,p)<1:continue
        break
    else:raise ValueError(('no exact local parameter',p))
    dep=vp(denominator(U,V),p)+2
    assert dep>=2
    cong.append((p,dep,U%p**dep,V%p**dep))
for p in FIX:
    w=16
    if p==2:
        v0=next(r for r in range(1,2**16,2) if r*r%2**16==b%2**16)
    else:
        v0=rootsmod(b,p,w)[0]
    U,V=1,v0
    ww,yy=conic(U,V)
    assert vp(ww,p)<=-5
    # Make the numerator depth fixed and the denominator at least as deep.
    dep=16
    cong.append((p,dep,U%p**dep,V%p**dep))
for p,d,u,ww in cong:
    pp=p**d
    a,m=crt(a,M,u,pp); v,n=crt(v,M,ww,pp); assert m==n
    M=m
K=isqrt(b)+1
U=a+M; V=K*U+(v-K*a)%M
WW,YY=conic(U,V)
assert WW>2 and WW*WW-b*YY*YY==theta
assert all(mod(WW,p*p)==Wt for p,Wt in cells)
assert all(vp(WW,p)<=-5 for p in FIX)
assert all(vp(WW*WW-theta,p)==1 and vp(YY,p)==0 for p in (p1,p2))
assert vp(WW,23)>=0 # proof cannot use saturation at original B
real=run('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
         '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
real['Ball'].precision=49152; real['Ball'].S=1<<49152
for step in range(20):
    hp=h+H*step
    ok,R=real['real_margin'](hp)
    if ok:break
else:raise ArithmeticError('no small real accepted h in this replay')
X0=real['Ball'].S//(2**64)
iv=[R.lo//X0,-((-R.hi)//X0)]
assert 100*min(map(abs,iv))>2**64 and iv[0]*iv[1]>0
print(json.dumps(dict(b=b,literal_J=J,actual_new_contacts=new,
    base_ternary_triple=[X,1,Z],h_prefix=h0,h_prefix_modulus=L0,
    final_h=hp,h_step=step,h_modulus=H,h_bitlength=hp.bit_length(),real_norm_interval_div_2pow64=iv,
    all_W_target_p2=[[p,w] for p,w in cells],local_parameter_residues=cong,
    chosen_global_param=[U,V],actual_scaled_pair_W=[WW.numerator,WW.denominator],
    actual_scaled_pair_Y=[YY.numerator,YY.denominator],
    fixed_pair_bad_W_depths={p:vp(WW,p) for p in FIX},
    full_B_incompatibility_prime=23,
    W_real_gt_2=True),indent=2))
