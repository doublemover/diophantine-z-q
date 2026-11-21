#!/usr/bin/env python3
"""One exact fixed-p_a numeric genus-one cover, at every completion; no Q point."""
from pathlib import Path
from hashlib import sha256
# Only load the import/arith prelude of the exact frozen b-only donor. No execution
# of the donor's separate b-specific conic, search, or real-proof branch.
P=Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py'
data=P.read_bytes()
assert sha256(data).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(data.decode().split('\nqs=(')[0], globals())
from sys import argv
variant=int(argv[1]) if len(argv)>1 else 1
assert variant in (1,2)
qa=(163199081,11941,4540,10317486,2039690,40805741)
bs1=((7497601,2399,1320,1562975,31260,15481),(25515769,5037,380,2021933,1594106,6381461))
bs2=((16990081,2209,3480,13934422,849725,29489),(17238721,1761,3760,1445536,107720,4310561))
bs=(bs1 if variant==1 else bs2)
qs=(qa,*bs); pA=415721
pAq,q1,q2=[x[0] for x in qs]
a=pA*pAq; b=q1*q2; D=a*b
assert a==67845285152401 and b in (191307055170169,292887266126401)
assert D in (12979281709686225818153925769,19871020087852834114214638801)
local=(3,5,7,11,37,2399)
aphase=tuple(chi(pA,p) for p in local); bphase=tuple(chi(9807649,p) for p in local)
assert aphase==(-1,1,-1,1,1,1) and bphase==(1,1,-1,1,-1,1)
assert chi(pA,pAq)==chi(q1,q2)==1
assert [(chi(z,pA),chi(z,pAq)) for z in (q1,q2)]==[(-1,-1),(1,1)]
assert all(chi(a,z)==1 for z in (q1,q2))
T=F(1,2399); Sl=F(-32,407); delta=T-Sl
Bbad=(2,3,5,7,11,37,2399)
assert a%8==b%8==1 and all(chi(a,p)==chi(b,p)==1 for p in Bbad if p!=2)
assert chi(b,23)==-1
h,H=h0,L0
new=[]
for item in qs:
    p,A,C,rr,o1,o2=item
    assert isprime(p) and p>76176 and p%8==1 and gcd(p,L0*Sprod)==1
    assert tuple(chi(p,z) for z in local)==(aphase if p==pAq else bphase)
    assert A*A+C*C==p and A%2==1 and C%2==0 and rr*rr%p==2
    Gs=(p+1-2*A,p+1+2*A); g=gcd(*Gs)
    assert g&(g-1)==0 and gcd(prod(Gs),Sprod*(pAq*q1*q2//p))==1
    assert o2%2 and gcd(o1,o2)==1 and gcd(p,o1*o2)==1
    M=p*p; ar=[]
    for r,o in ((rr,o1),(p-rr,o2)):
        rr2=r+p*((2-r*r)//p*pow(2*r,-1,p)%p)
        order,P,U,formal=F0(p,rr2)
        assert order(Gs)==o
        z=P(o);assert formal(z) and z[1]==0 and vp(z[0],p)==1
        ls=labels(p*o)
        us=[U(P(v))[0] for v in ls];assert all(u%p for u in us)
        az=prod(-pow(u,-1,M) for u in us)%M
        ar.append(dict(r=r,r_p2=rr2,order=o,order_factorization=list(exponents(o)),
                       first_formal_z=z[0],labels=ls,U_p2=us,product=az))
    A1,A2=[r['product'] for r in ar]; c=[1,((A1+A2)*pow(2,-1,M)+A1*A2)%M,A1*A2%M]
    assert all(x%p for x in c)
    f=[F(j) for j in (0,F(-1,2),-1,T,Sl)]
    roots=[mod(rt,p)*pow(u*u,-1,p)%p for u in c for rt in f[1:]]
    assert len(set(roots))==12 and all(roots)
    marked,coef,other,oc=(Sl,a,T,b) if p==pAq else (T,b,Sl,a)
    assert tuple(chi(mod(z,p),p) for z in (Sl,T,delta))==((1,1,-1) if p==pAq else (-1,1,1))
    w0=rootsmod(mod(marked,M)+coef,p,2)[0]; w=mod(F(w0,c[1]),M)
    vals=[pow(u*w,2,M) for u in c]
    Fvals=[prod(v-mod(z,M) for z in f)%M for v in vals]
    assert not Fvals[1]%p and Fvals[1] and Fvals[0]%p and Fvals[2]%p
    assert all((v-1)%p for v in vals)
    assert chi(mod((F(w0*w0)-other)/oc,p),p)==1
    for e,ed in ((0,o1),(1,o2),(p**3,p**4)):h,H=crt(h,H,e,ed)
    new.append(dict(p=p,AB=[A,C],counts=Gs,arms=ar,scales_mod_p2=c,W_mod_p2=w0,
                    w_mod_p2=w,T_rows=vals,F_rows=Fvals,contact='S' if p==pAq else 'T'))
assert h%L0==h0 and H%L0==0 and h%64==0
old=[]
for row in S:
    p=row['prime'];m=p*p
    W=row['scales_mod_p2'][1]*row['r_over_d_mod_p2']%m
    z, y=(F(W)**2-Sl)/a,(F(W)**2-T)/b
    assert vp(z,p)==vp(y,p)==0
    zr=mod(z,p);yr=mod(y,p)
    assert chi(zr,p)==chi(yr,p)==1
    old.append([p,W,zr,yr])
assert len(old)==16
real=run('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
       '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
prec=int(argv[2]) if len(argv)>2 else 32768
real['Ball'].precision=prec;real['Ball'].S=1<<prec
for k in range(20):
    hp=h+H*k
    ok,Rr=real['real_margin'](hp)
    if ok:break
else:raise ArithmeticError('no real accepted representative found in budget')
Z=real['Ball'].S//2**64
iv=Rr.lo//Z,-((-Rr.hi)//Z)
assert 100*min(map(abs,iv))>2**64 and iv[0]*iv[1]>0
print(json.dumps(dict(a=a,b=b,D=D,literal_J=J,actual_new_contacts=new,
    old_cells_W_a_unit_b_unit=old,h_prefix=h0,h_prefix_modulus=L0,
    final_h=hp,h_step=k,h_modulus=H,h_bitlength=hp.bit_length(),
    real_interval_div_2pow64=iv,complete_elliptic_bad_support=list(Bbad)+[pA,pAq,q1,q2],
    B_missing_square_at=23),indent=2))
