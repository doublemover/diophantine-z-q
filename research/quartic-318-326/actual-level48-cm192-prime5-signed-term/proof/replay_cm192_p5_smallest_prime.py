#!/usr/bin/env python3
"""A fixed-characteristic evaluator: no n, trace, norm-term scan, or h needed."""
from fractions import Fraction
import json

# Characteristic-zero path check in the basis 1,sqrt(2),sqrt(3),sqrt(6).
def vv(a):
    return a if isinstance(a, tuple) else (Fraction(a),0,0,0)
def aa(a,b):
    return tuple(x+y for x,y in zip(vv(a),vv(b)))
def mm(a,b):
    r=[Fraction(0)]*4
    for i,x in enumerate(vv(a)):
        for j,y in enumerate(vv(b)):
            r[i^j] += x*y*(2 if i&j&1 else 1)*(3 if i&j&2 else 1)
    return tuple(r)
def ss(a,b):return aa(a,mm(-1,b))
def pp(a,n):
    r=vv(1)
    for _ in range(n):r=mm(r,a)
    return r
def gg(a,b):
    c=vv(1)
    for k in (1,2,3):
        c=mm(c,tuple((-1)**((i&k).bit_count())*x for i,x in enumerate(vv(b))))
    d=mm(b,c)
    assert d[0]!=0 and not any(d[1:])
    return mm(a,mm(1/d[0],c))
R2=(0,1,0,0);R3=(0,0,1,0)
def zero_characteristic(sign):
    a=b=0
    e2=ss(ss(-3,mm(6,R3)),mm(sign,mm(aa(6,mm(2,R3)),R2)))
    for j,e in enumerate((-1,ss(-3,mm(2,R3)),e2)):
        assert aa(mm(e,aa(aa(pp(e,2),mm(a,e)),b)),int(j==0))==vv(0)
        A=aa(a,mm(3,e));B=aa(aa(mm(3,pp(e,2)),mm(2,mm(a,e))),b)
        a,b=mm(-2,A),ss(pp(A,2),mm(4,B))
    jc=gg(mm(256,pp(ss(pp(a,2),mm(3,b)),3)),mm(pp(b,2),ss(pp(a,2),mm(4,b))))
    X=aa(1,mm(sign,R2));y48=mm(aa(3,mm(2,R3)),pp(X,2))
    u=aa(ss(X,2),gg(mm(3,X),y48))
    for d in (2,4,16):u=gg(pp(u,2),aa(u,d))
    j=gg(pp(aa(u,256),3),pp(u,2))
    assert jc==j
    return [int(x) for x in j]
CHARZERO={str(sign):zero_characteristic(sign) for sign in (1,-1)}
assert CHARZERO["1"] != CHARZERO["-1"]

p=5; n=32; Q=p**n; M=5**16-1; sh=10; mask=1023
FIVE=sum(5<<(sh*i) for i in range(n))
ONE=1
def digits(a):
    return tuple((a>>(sh*i))&mask for i in range(n))
def normalize(a):
    return sum((((a>>(sh*i))&mask)%5)<<(sh*i) for i in range(n))
def add(a,b): return normalize(a+b)
def sub(a,b): return normalize(a+FIVE-b)
def neg(a): return sub(0,a)
def mul(a,b):
    z=a*b
    return sum((((((z>>(sh*i))&mask)+2*((z>>(sh*(i+n)))&mask))%5)<<(sh*i))
               for i in range(n))
def ex(a,k):
    y=1
    while k:
        if k&1:y=mul(y,a)
        a=mul(a,a);k//=2
    return y
def div(a,b):
    assert b
    return mul(a,ex(b,Q-2))
def rat(z): return z%5
def mulc(k,a):return mul(k%5,a)
def short(a):return {str(i):c for i,c in enumerate(digits(a)) if c}
T=1<<sh
assert ex(T,32)==2 and ex(T,64)==4 and ex(T,128)==1
assert pow(5,32,128)==1 and pow(5,16,128)!=1
s2=ex(T,16);r3=mulc(2,s2);s17=s2
assert mul(s2,s2)==2 and mul(r3,r3)==3
omega=mulc(3,add(1,s2))  # sqrt(-3)=sqrt(2) in this chosen residue field
assert add(sub(mul(omega,omega),omega),1)==0
AUT=neg(omega)

ODD=Q-1; e=0
while ODD%2==0:
    ODD//=2;e+=1
assert e==7 and ex(T,(Q-1)//2)==4
def root(a):
    if a==0:return 0
    if ex(a,(Q-1)//2)!=1:return None
    t=ex(a,ODD);r=ex(a,(ODD+1)//2);c=ex(T,ODD);m=e
    while t!=1:
        z=t;i=0
        while z!=1:
            z=mul(z,z);i+=1
        assert i<m
        b=ex(c,2**(m-i-1));c=mul(b,b)
        t=mul(t,c);r=mul(r,b);m=i
    assert mul(r,r)==a
    return r

def addcurve(P,R,a=0,b=0):
    if P is None:return R
    if R is None:return P
    x,y=P;u,v=R
    if x==u and add(y,v)==0:return None
    if x==u:
        assert y==v
        t=div(add(add(mulc(3,mul(x,x)),mulc(2,mul(a,x))),b),mulc(2,y))
    else:
        t=div(sub(v,y),sub(u,x))
    S=sub(sub(sub(mul(t,t),a),x),u)
    return S,sub(mul(t,sub(x,S)),y)
def nP(k,P):
    if k<0:return nP(-k,negP(P))
    R=None
    while k:
        if k&1:R=addcurve(R,P)
        P=addcurve(P,P);k//=2
    return R
def negP(P):return None if P is None else (P[0],neg(P[1]))
def omP(P):return None if P is None else (mul(AUT,P[0]),neg(P[1]))
def fr(P):return None if P is None else (ex(P[0],5),ex(P[1],5))

seeds=[]
for k in range(1,128):
    x=add(T,add(mulc(k//5,ex(T,2)),k%5))
    y=root(add(ex(x,3),1))
    if y is not None:
        P=(x,y)
        assert nP(M,P) is None
        seeds.append(P)
    if len(seeds)>=11:break
def point(l):
    for P in seeds:
        A=nP(M//l,P)
        if A is not None and nP(l//(2 if l==64 else l),A) is not None:
            assert nP(l,A) is None
            return A
    raise ValueError("increase deterministic seeds")
P64=point(64);P17=point(17)
def multip(l,P):
    a=[None]
    for i in range(1,l):a.append(addcurve(a[-1],P))
    assert addcurve(a[-1],P) is None
    return a
def find_pair(l,P,R):
    a={V:i for i,V in enumerate(multip(l,P))}
    for j,V in enumerate(multip(l,omP(P))):
        w=addcurve(R,negP(V))
        if w in a:return a[w],j
    raise Exception("not in generated torsion")
eta64=find_pair(64,P64,fr(P64));eta17=find_pair(17,P17,fr(P17))
assert nP(2,fr(fr(P64)))==nP(-10,P64)

def chain(P,branch):
    sqrt2=mulc(branch,s2)
    e0=-1%5;e1=neg(add(3,mulc(2,r3)))
    e2=sub(neg(add(3,mulc(6,r3))),mul(add(6%5,mulc(2,r3)),sqrt2))
    a=0;b=0; e=e0
    for j,e in enumerate((e0,e1,e2)):
        A=add(a,mulc(3,e));B=add(add(mulc(3,mul(e,e)),mulc(2,mul(a,e))),b)
        # e is a root of the current model: for the first model RHS x^3+1,
        # subsequently the constant is zero.
        assert add(mul(e,add(add(mul(e,e),mul(a,e)),b)),1 if j==0 else 0)==0
        if P is not None:
            x,y=P;u=sub(x,e)
            if u==0:
                assert y==0;P=None
            else:
                P=add(add(u,A),div(B,u)),mul(y,sub(1,div(B,mul(u,u))))
        a,b=mulc(-2,A),sub(mul(A,A),mulc(4,B))
        if P is not None:
            x,y=P
            assert mul(y,y)==mul(x,add(add(mul(x,x),mul(a,x)),b))
    return P,a,b

P8=nP(8,P64)
def normpair(a,b):return a*a+a*b+b*b
def prodpair(x,y,l):
    a,b=x;c,d=y
    return (a*c-b*d)%l,(a*d+b*c+b*d)%l
def invpair(x,l):
    a,b=x;c=pow(normpair(a,b),-1,l)
    return (a+b)*c%l,-b*c%l
def conjpair(x,l):return (x[0]+x[1])%l,(-x[1])%l
def jcurve(a,b):
    return div(mulc(256,ex(sub(mul(a,a),mulc(3,b)),3)),
               mul(mul(b,b),sub(mul(a,a),mulc(4,b))))
branches={}
for branch in (1,-1):
    w0=[]
    for a in range(8):
        for b in range(8):
            P=addcurve(nP(a,P8),nP(b,omP(P8)))
            S,A,B=chain(P,branch)
            if S is None and normpair(a,b)%2:
                w0.append((a,b))
    assert len(w0)==4
    w=min(w0)
    eta=prodpair(prodpair(eta64,conjpair(w,64),64),invpair(w,64),64)
    assert normpair(*eta)%64==(-5)%64
    X=add(1,mulc(branch,s2))
    Y48=mul(add(3,mulc(2,r3)),mul(X,X))
    u=add(sub(X,2),div(mulc(3,X),Y48))
    for b in (2,4,16):u=div(mul(u,u),add(u,b%5))
    j=div(ex(add(u,256%5),3),mul(u,u))
    assert jcurve(A,B)==j
    branches[str(branch)]={"2_primary_cyclic_8_kernel_generators":w0,"eta_at2_mod64":eta,
                           "quotient_a_b":[short(A),short(B)],"checked_j":short(j)}

def line(P,R,Z):
    x,y=P;u,v=R;z,w=Z
    if x==u and add(y,v)==0:
        return sub(z,x),None
    if x==u:
        s=div(mulc(3,mul(x,x)),mulc(2,y))
    else:
        s=div(sub(v,y),sub(u,x))
    S=addcurve(P,R)
    assert S is not None
    return div(sub(sub(w,y),mul(s,sub(z,x))),sub(z,S[0])),S
def mill(P,Z):
    R=P;f=1
    for bit in (0,0,0,1):  # 17 = 10001
        t,R=line(R,R,Z);f=mul(mul(f,f),t)
        if bit:t,R=line(R,P,Z);f=mul(f,t)
    assert R is None
    return f
U=omP(P17)
zeta0=None
for S in seeds:
    try:
        ls=(mill(P17,addcurve(U,S)),mill(P17,S),
            mill(U,negP(S)),mill(U,addcurve(P17,negP(S))))
        if all(ls):
            val=div(mul(ls[0],ls[2]),mul(ls[1],ls[3]))
            assert val!=1 and ex(val,17)==1
            zeta0=val;break
    except (AssertionError,TypeError):
        pass
assert zeta0 is not None
gauss=0
for j in range(1,17):
    gauss=add(gauss,mulc(1 if pow(j,8,17)==1 else -1,ex(zeta0,j)))
assert mul(gauss,gauss)==2
assert gauss in (s17,neg(s17))
assert eta64==(22,17) and eta17==(2,2)
assert branches["1"]["eta_at2_mod64"]==(1,22)
assert branches["-1"]["eta_at2_mod64"]==(61,38)
assert gauss==s17
print(json.dumps({"characteristic_zero_matched_quotient_j":CHARZERO,"field":"F5[T]/(T^32-2)", "sqrt2_sqrt17":short(s2),"sqrt3":short(r3),
  "j0_eta_source":{"mod64":eta64,"mod17":eta17},
  "j0_torsion_basis_first_point":{"64":[short(x) for x in P64],"17":[short(x) for x in P17]},
  "level48_two_fixed_flags":branches,
  "Weil_value_e17_P_omegaP":short(zeta0),
  "Gauss_value_in_anchor_sqrt17_units":1 if gauss==s17 else -1,
  "spin_constant":1 if gauss==s17 else -1,
  "scope":"fixed local p5 only; no selected n, no embedding norm counts or mark"},
  sort_keys=True,indent=2))
