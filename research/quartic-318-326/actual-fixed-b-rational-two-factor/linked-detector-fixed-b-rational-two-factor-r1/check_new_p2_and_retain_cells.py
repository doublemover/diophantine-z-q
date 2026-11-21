#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from math import gcd,prod
import json,sys
from gmpy2 import mpz
sys.set_int_max_str_digits(0)
src=(Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py')
assert sha256(src.read_bytes()).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(compile(src.read_text().split('\nqs=(')[0].replace('Path(__file__).resolve().parent.parent','Path('+repr(str(src.parent.parent))+')'),str(src),'exec'))
import inspect
exec(inspect.getsource(F0).replace('isinstance(P[0],int)','isinstance(P[0],(int,mpz))'),globals())
F0=field
w0,w1=sys.argv[1:]
C=json.loads(Path(w0).read_bytes())
G=json.loads(Path(w1).read_bytes())
W,Y=F(*C['W']),F(*C['Y'])
p=mpz(C['qa'])
a=415721*int(p); b=C['b'];z=C['cofactor_square_root']
assert W*W-F(-32,407)==F(a*z*z,W.denominator**2)
assert W*W-F(1,2399)==b*Y*Y
assert all(vp(W,l)==v for l,v in [(2,-600),(3,-8),(17,-1)])
J1=json.loads((root/'linked-detector-numeric-anchor-phase-repair-r1'/'EXACT-PRIMARY-REPAIRED-COVER.json').read_bytes())
for q,val,z0,z1 in J1['old_cells_W_a_unit_b_unit']:assert mod(W,q*q)==val
for r in J1['actual_new_contacts'][1:]:assert mod(W,r['p']**2)==r['W_mod_p2']
o,(h,H)=G['compatible'][0]
q2,H0,H1,rt,rt2,Ar,Br=o
assert q2==p and rt+rt2==p and Ar*Ar+Br*Br==p
print('p² verification bit length',p.bit_length(),file=sys.stderr,flush=True)
assert h%L0==h0 and H%L0==0 and h%289==204 and h%64==0
assert h%p**4==p**3 and h%H0==0 and h%H1==1 and gcd(H0,H1)==1
assert gcd(p,2*H0*H1)==1
gs=(p+1-2*Ar,p+1+2*Ar)
assert gcd(*gs)&(gcd(*gs)-1)==0
B=prod(t['prime'] for t in S)*prod(t['p'] for t in J1['actual_new_contacts'][1:])
assert gcd(prod(gs),B)==1
m=p*p
N=mpz(s-2)
def label(Nmax):
    dd=N;q=mpz(1)
    while (gg:=gcd(dd,Nmax))>1:
        q*=gg;dd//=gg
    sc=Nmax*q;x,y=mpz(0),mpz(1);K=mpz(s)%sc
    for b in KB:
        X=x*(2*y-K*x)%sc;Y=(y*y-x*x)%sc
        x,y=(X,Y) if b=='0' else (Y,(K*Y-X)%sc)
    assert x%q==0
    a=Nmax
    return (mpz(3723)%a,mpz(s)%a,y%a,x//q*pow(dd,-1,a)%a)
ends=[]
for r,ann in ((rt,H0),(rt2,H1)):
    rt_lift=mpz(r)+p*((2-mpz(r)*r)//p*pow(mpz(2)*r,-1,p)%p)
    assert rt_lift**2%m==2
    _,P,U,formal=F0(p,rt_lift)
    R=P(mpz(ann));assert formal(R) and R[1]==0 and R[0]%p==0
    ls=label(p*ann)
    UU=[U(P(k))[0] for k in ls]
    assert all(u%p for u in UU)
    A=prod(-pow(u,-1,m) for u in UU)%m
    ends.append(dict(root_mod_p=r,root_mod_p2=rt_lift,ann=ann,ann_return_z_p2=R[0],literal_labels=ls,U_p2=UU,inverse_product=A))
    print('finite arm verified',file=sys.stderr,flush=True)
A,A2=[r['inverse_product'] for r in ends]
cc=[1,((A+A2)*pow(mpz(2),-1,m)+A*A2)%m,A*A2%m]
assert all(c%p for c in cc)
tt=mpz(mod(W,int(m)))*pow(cc[1],-1,m)%m
roots=[0,F(-1,2),F(-1),F(-32,407),F(1,2399)]
rmods=[mpz(mod(r,int(m))) for r in roots]
fv=[prod((c*tt)**2-r for r in rmods)%m for c in cc]
assert all((c*tt)**2%p!=1 for c in cc)
assert fv[0]%p and fv[2]%p and fv[1] and not fv[1]%p
fields=[r*pow(c*c,-1,p)%p for c in cc for r in rmods[1:]]
assert all(fields) and len(set(fields))==12
print(json.dumps(dict(p=p,counts=gs,h=h,H=H,actual_arms=ends,c_mod_p2=cc,w_mod_p2=tt,F_mod_p2=fv,
    W=C['W'],Y=C['Y'],cofactor_square_root=z,
    selected_positive=[drop for drop in (415721,8912209,1185793321,int(p))]),default=int,indent=2))
