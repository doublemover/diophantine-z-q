from pathlib import Path
from fractions import Fraction as F
from math import gcd
from hashlib import sha256
import sys,json
sys.set_int_max_str_digits(0)
s0=(Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py')
assert sha256(s0.read_bytes()).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(compile(s0.read_text().split('\nqs=(')[0].replace('Path(__file__).resolve().parent.parent','Path('+repr(str(s0.parent.parent))+')'),str(s0),'exec'))
C=json.load(open(sys.argv[1]))
Jj=json.load(open(sys.argv[2]))
h,H=Jj['h'],Jj['H']; W=F(*C['W'])
R=[0,F(-1,2),-1,F(-32,407),F(1,2399)]
out=[]
for p in (94547,699211):
 assert isprime(p) and p>76176 and chi(2,p)==-1
 M=p*p;Ts=pow(mod(W,M),2,M);Fv=prod((Ts-mod(z,M))%M for z in R)%M
 assert vp(Fv,p)==1 and (Ts-1)%p
 cnt=(p+chi(7,p))**2
 order,P,U,formal=F0(p,None); o=order((cnt,)); ls=labels(o*p)
 UU=[U(P(n)) for n in ls]
 NR=lambda q,m:(q[0]*q[0]-2*q[1]*q[1])%m
 MT=lambda u,v,m:((u[0]*v[0]+2*u[1]*v[1])%m,(u[0]*v[1]+u[1]*v[0])%m)
 assert all(NR(a,M)%p for a in UU)
 GG=(1,0)
 for z in UU:
  q=-pow(NR(z,M),-1,M)
  GG=MT(GG,(q*z[0],-q*z[1]),M)
 cs=[1,(GG[0]+NR(GG,M))%M,NR(GG,M)]
 assert all(c%p for c in cs)
 a2=lambda x,y:((x[0]+y[0])%p,(x[1]+y[1])%p)
 sc=lambda x,k:(x[0]*k%p,x[1]*k%p)
 mm=lambda x,y:MT(x,y,p)
 no=lambda x:NR(x,p)
 def inv(x):return sc((x[0],-x[1]),pow(no(x),-1,p))
 one=(1,0); d0=(11%p,-6%p);k=(-1%p,7*pow(4,-1,p)%p);m=(39*pow(8,-1,p)%p,-9*pow(2,-1,p)%p)
 def chart(ind):
  Q=P(ind%o)
  if formal(Q):return (0,0),one
  x,y=[tuple(v%p for v in zz) for zz in Q];x2=mm(x,x);d=a2(x2,d0)
  u=mm(sc(y,2),inv(d))
  w=mm(a2(a2(mm(x2,x2),sc(mm(d0,x2),-6)),mm(d0,d0)),inv(mm(d,d)))
  return u,w
 u,v=chart(h)
 assert no(u)
 k2=mm(k,k);u2=mm(u,u)
 Sh=mm(a2(mm(mm(k,v),inv(u)),sc(m,-1)),inv(a2(k2,mm(d0,u2))))
 g=mm(u2,mm(Sh,Sh));x=mm(d0,mm(g,g));y=mm(x,x)
 PG=a2(a2(one,sc(x,-61*pow(65,-1,p))),sc(y,16*pow(195,-1,p)))
 QG=a2(one,sc(x,-7*pow(13,-1,p)))
 B=a2(a2(k2,mm(m,Sh)),mm(d0,g))
 Common=mm(mm(k,Sh),mm(PG,inv(mm(B,QG))))
 assert no(Common)
 pv=[];oq=[]
 for n in ls:
  _,V0=chart(n*h)
  _,V1=chart(n*(h-1))
  pv.append(no(V0));oq.append(no(a2(one,sc(a2(V1,(-1,0)),5*pow(13,-1,p)))))
 assert all(pv) and all(oq[1:])
 # first exact leaf at depth -7; the next two are bounded below at -1;
 # all later leaves are at worst -25; no cancellation. Leading term rational.
 vfold=-7*2**15;vpole=1+2*vfold
 out.append(dict(p=p,e=1,arm_order=o,count=cnt,stable_h_modulus=o*p,h_mod_o_p=h%(o*p),
    literal_T_mod_p2=Ts,F_mod_p2=Fv,scales_p2=cs,arbitrary_numerically_same_h_mod_o=h%o,
    actual_U_h_mod_p=u,actual_V_h_mod_p=v,actual_NormU_h_mod_p=no(u),
    PG_QG_common_norm_mod_p=[no(PG),no(QG),no(Common)],primary_V_norm_mod_p=pv,
    alternate_QJ_norm_mod_p=oq,weighted_first_depth=-7,fold_and_trace_depth=vfold,
    literal_pole_depth=vpole,reduced_denominator_exponent=-vpole))
print(json.dumps(dict(fatal=out),indent=2))
