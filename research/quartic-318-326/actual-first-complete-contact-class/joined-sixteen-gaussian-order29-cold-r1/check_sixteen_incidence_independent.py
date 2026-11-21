#!/usr/bin/env python3
"""Independent finite lifted group/CRT and real enclosure for the CM29 incidences and retained fourteen CRT."""
from pathlib import Path
from math import isqrt, prod, gcd, lcm
from hashlib import sha256
import json, sys
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING
def read_pin(arg, expected):
    raw=Path(arg).read_bytes()
    assert sha256(raw).hexdigest()==expected
    return json.loads(raw)
A=read_pin(sys.argv[1],'5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7')
B=read_pin(sys.argv[2],'d6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c')
O=read_pin(sys.argv[3],'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec')
S=read_pin(sys.argv[4],'d8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0')
XII=read_pin(sys.argv[5],'b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744')
XIV=read_pin(sys.argv[6],'0d8a8a51bc89c1ba66dee18f22eb40ac51b2b681d227be212517915c7f535efc')
T=read_pin(sys.argv[7],'6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1')
old=O['rows']+S['rows']+XII['rows']+XIV['rows']
assert len(old)==14 and len(T['rows'])==2
assert len({x['prime'] for x in old+T['rows']})==16
assert int(XIV['simultaneous_h_modulus'])==int(T['prior_fourteen_h_modulus'])
assert int(XIV['simultaneous_h_residue'])==int(T['prior_fourteen_h_residue'])

class FieldLift:
    def __init__(self,p):
        self.p=p
        self.m=p*p
    def elt(self,a,b=0): return (a%self.m,b%self.m)
    def add(self,x,y): return self.elt(x[0]+y[0],x[1]+y[1])
    def neg(self,x): return self.elt(-x[0],-x[1])
    def sub(self,x,y): return self.add(x,self.neg(y))
    def mul(self,x,y): return self.elt(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    def scale(self,a,x): return self.elt(a*x[0],a*x[1])
    def inv(self,x):
        z=pow((x[0]**2-2*x[1]**2)%self.m,-1,self.m)
        return self.scale(z,(x[0],-x[1]))
    def sq(self,x): return self.mul(x,x)
    def res(self,x): return tuple(i%self.p for i in x)
    def unit(self,x): return bool(self.res(x)!=(0,0))

def kernel(p,r):
    R=FieldLift(p)
    e=R.elt(0,1) if r is None else R.elt(r+p*(((2-r*r)//p)*pow(2*r,-1,p)%p))
    assert R.sq(e)==R.elt(2)
    d=R.sub(R.elt(3),e)
    A=R.neg(R.sq(d))
    P=('a',(R.add(R.elt(1),e),R.scale(2,e)))
    fe=lambda z:('f',z)
    def diff(x): return R.add(R.scale(3,R.sq(x)),A)
    def tplus(P,z):
        kind,v=P
        if kind=='f': return fe(R.add(v,z))
        x,y=v
        return ('a',(R.add(x,R.scale(2,R.mul(y,z))),R.add(y,R.mul(diff(x),z))))
    def decide(x,y,k,w,xx_sum):
        X=R.sub(R.sq(k),R.mul(xx_sum,R.sq(w)))
        Y=R.sub(R.mul(k,R.sub(R.mul(x,R.sq(w)),X)),R.mul(y,R.mul(R.sq(w),w)))
        if R.unit(w):
            n=R.inv(w)
            return ('a',(R.mul(X,R.sq(n)),R.mul(Y,R.mul(R.sq(n),n))))
        assert R.unit(X) and R.unit(Y)
        return fe(R.neg(R.mul(R.mul(X,w),R.inv(Y))))
    def secant(P,Q):
        x,y=P; u,v=Q
        return decide(x,y,R.sub(v,y),R.sub(u,x),R.add(x,u))
    def double(P):
        x,y=P
        return decide(x,y,diff(x),R.scale(2,y),R.scale(2,x))
    def add(P,Q):
        if P[0]=='f': return tplus(Q,P[1])
        if Q[0]=='f': return tplus(P,Q[1])
        X=P[1]; Y=Q[1]
        if X==Y: return double(X)
        x,y=X; u,v=Y
        if R.res(x)!=R.res(u) or R.res(y)!=R.res(v):
            return secant(X,Y)
        if R.unit(y):
            z=secant(X,(u,R.neg(v)))
            assert z[0]=='f'
            return tplus(double(Y),z[1])
        root=next(t for t in ((0,0),d,R.neg(d)) if R.res(t)==R.res(x))
        return fe(R.mul(R.add(y,v),R.inv(diff(root))))
    def times(n):
        A=fe((0,0)); B=P
        # LSB order differs from original left-to-right fixed-R ladder.
        while n:
            if n&1: A=add(A,B)
            n>>=1
            if n: B=add(B,B)
        return A
    return times

hh=int(T['real_passing_h']);h0=int(A['h']);L=int(B['preserved_old_modulus'])
assert L==int(XII['old_h_preserved_modulus'])
J=int(A['J']); assert J==int(T['literal_scalar_J'])
idx=6**15*3**65536*J; assert idx%h0==0
s=idx+1; k=2*(s-2)
rr,den=int(T['numeric_test_r']),T['numeric_test_d']
assert gcd(rr,den)==1 and rr*rr>2*den*den and rr%(2*3*17)==1
def labels(N,factors):
    e=s-2; adjust=1
    for p in factors:
        while e%p==0:e//=p;adjust*=p
    P=N*adjust
    a,b,c,d=1,0,0,1
    x,y,z,w=s%P,P-1,1,0
    n=k
    while n:
        if n&1:a,b,c,d=(a*x+b*z)%P,(a*y+b*w)%P,(c*x+d*z)%P,(c*y+d*w)%P
        n>>=1
        if n:x,y,z,w=(x*x+y*z)%P,(x*y+y*w)%P,(z*x+w*z)%P,(z*y+w*w)%P
    assert c%adjust==0 and gcd(e,N)==1
    return [3723%N,s%N,a%N,(c//adjust)*pow(e,-1,N)%N]
moduli=[L]; modulo=1
for prev in (O,S,XII,XIV):
    assert hh%int(prev['simultaneous_h_modulus'])==int(prev['simultaneous_h_residue'])
    assert rr%int(prev['numeric_r_modulus'])==int(prev['numeric_test_r'])
for row in old:
    p=row['prime']; m=p*p
    N,M=(a['order'] for a in row['arms'])
    assert hh%N==0 and hh%M==1 and hh%p**4==p**3
    assert rr*pow(den,-1,m)%m==row['r_over_d_mod_p2']
    moduli.extend((N,M,p**4)); modulo=lcm(modulo,m)
n0,L0=(int(XIV[k]) for k in ('simultaneous_h_residue','simultaneous_h_modulus'))
assert n0%2==L0%2==0 and n0%29==1 and L0%29==0
for Lrow in T['rows']:
    p=Lrow['prime'];m=p*p
    i,j=Lrow['assigned_scale'],Lrow['assigned_root_index']
    assert (i,j) in ((1,4),(2,3))
    assert pow(p,3,7)==6 and p%29!=1
    assert p>76176 and p%8==1 and all(p%q for q in range(2,isqrt(p)+1))
    aa,bb=Lrow['AB']; assert p==aa*aa+bb*bb
    fprod=[]; orders=[]
    for arm in Lrow['arms']:
        r=arm['root'];root=arm['root_p2'];a=arm['order']; periods=p*a
        assert root%p==r and root*root%m==2 and periods==arm['label_period']
        fn=kernel(p,r)
        assert fn(a)==('f',tuple(arm['formal_first_z'])) and fn(a)[1]!=(0,0)
        checks=set(arm['order_prime_divisors'])
        b=a
        for q in checks:
            assert 1<q and all(q%v for v in range(2,isqrt(q)+1)) and a%q==0
            assert fn(a//q)[0]=='a'
            while b%q==0:b//=q
        assert b==1
        ell=labels(periods,checks|{p});assert ell==arm['literal_labels']
        d=(3-root)**2%m
        vals=[]
        for e in ell:
            typ,(xy)=fn(e);assert typ=='a'
            x,y=(v[0] for v in xy);assert all(v[1]==0 for v in xy)
            vals.append(2*y*pow((x*x+d)%m,-1,m)%m)
        assert vals==arm['U_values'] and all(gcd(x,m)==1 for x in vals)
        ff=prod(-pow(v,-1,m) for v in vals)%m
        assert ff==arm['product_fixedRoots']
        fprod.append(ff);orders.append(a)
    a,b=fprod
    c2=a*b%m;c1=((a+b)*pow(2,-1,m)+c2)%m
    cs=[1,c1,c2]; assert cs==Lrow['scales_mod_p2'] and all(gcd(c,m)==1 for c in cs)
    theta=[-pow(2,-1,m)%m,m-1,pow(2399,-1,m),-32*pow(407,-1,m)%m]
    SS=[(v*pow(c*c,-1,p))%p for c in cs for v in theta]
    assert SS==Lrow['distinct_nonzero_scaled_roots_mod_p'] and 0 not in SS and len(set(SS))==12
    assert (rr*pow(den,-1,m))%m==Lrow['r_over_d_mod_p2']
    TT=[(c*rr*pow(den,-1,m))**2%m for c in cs]
    FF=[prod((t-u)%m for u in [0,*theta])%m for t in TT]
    assert TT==Lrow['T_j_mod_p2'] and FF==Lrow['contact_values_mod_p2'] and TT[i]==(p+theta[j-1])%m
    assert FF[i]%p==0 and FF[i]!=0 and all(FF[jj]%p for jj in range(3) if jj!=i)
    assert all(t%p!=1 for t in (TT[i],))
    assert all(gcd(p,v)==1 for v in (2,2399,407,3,2398,439))
    assert hh%orders[0]==0 and hh%orders[1]==1 and hh%p**4==p**3
    moduli.extend([*orders,p**4])
    modulo=lcm(modulo,m)
    print(p,orders,cs,FF)
assert hh%L==h0%L and hh%5==0 and h0%5==0
assert lcm(*moduli)==int(T['simultaneous_h_modulus'])
hmin=int(T['simultaneous_h_residue'])
assert 0<hmin<lcm(*moduli)
assert hh==hmin+T['real_passing_step']*lcm(*moduli)
assert lcm(2*3*17,modulo)==int(T['numeric_r_modulus'])
assert 0<rr<lcm(2*3*17,modulo)

# Independent degree29 denominator: apply Gaussian multiplier upstairs, then quotient.
from fractions import Fraction as Fr
def el(*a):return tuple(map(Fr,(*a,*([0]*(4-len(a))))))
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def minus(a,b):return tuple(x-y for x,y in zip(a,b))
def sc(a,n):return tuple(n*x for x in a)
def m(a,b):
 c=[0]*4
 for j,x in enumerate(a):
  for k,y in enumerate(b):
   z=j&k
   c[j^k]+=x*y*(2 if z&1 else 1)*(-1 if z&2 else 1)
 return tuple(c)
def conj(a,s):return tuple((-x if j&s else x) for j,x in enumerate(a))
def div(a,b):
 z=m(m(conj(b,1),conj(b,2)),conj(conj(b,1),2))
 norm=m(b,z)
 assert norm[0] and norm[1:]==(0,0,0)
 return sc(m(a,z),1/norm[0])
A=el(-11,6); R=el(1,1),el(0,2)
def Padd(P,Q):
 if P is None:return Q
 if Q is None:return P
 x,y=P; u,v=Q
 if x==u and plus(y,v)==el(0):return None
 s=div(plus(sc(m(x,x),3),A),sc(y,2)) if P==Q else div(minus(v,y),minus(u,x))
 X=minus(minus(m(s,s),x),u)
 Y=minus(m(s,minus(x,X)),y)
 assert m(Y,Y)==m(X,plus(m(X,X),A))
 return X,Y
P2=Padd(R,R);P4=Padd(P2,P2);P5=Padd(P4,R)
IP2=sc(P2[0],-1),m(el(0,0,1),P2[1])
X=Padd(P5,IP2)[0]; phiX=plus(X,div(A,X))
den_cm=lcm(*(x.denominator for x in phiX))
dc=int(T['x_denominator_sqrt_exact'])
roster=T['x_denominator_sqrt_prime_factors']
assert dc*dc==den_cm and int(prod(roster))==dc
assert all(p%8==1 and p%29!=1 and all(p%j for j in range(2,isqrt(p)+1)) for p in roster)
assert tuple(int(x*den_cm) for x in phiX)==tuple(map(int,T['x_scaled_numerators']))
print('CM denominator independent via upstairs [5+2I]R then phi',dc)
left=[]
n0_H=int(XIV['simultaneous_h_residue'])
for row in T['exact_order_29_candidate_roster']:
 p=row['prime']; assert p in roster and p>76176
 n,m=row['actual_orders']; rs=row['roots']; assert sum(rs)==p and all(t*t%p==2 for t in rs)
 actual_mids=[]
 for r,n0 in zip(rs,(n,m)):
  fn=kernel(p,r); checks=[d for d in range(2,isqrt(n0)+1) if n0%d==0 and all(d%l for l in range(2,isqrt(d)+1))]
  z=n0
  for k in checks:
   while z%k==0:z//=k
  if z!=1:checks.append(z)
  assert fn(n0)[0]=='f' and all(fn(n0//l)[0]=='a' for l in checks)
  j=fn(n0//2) if n0%2==0 else None
  if j is not None:assert j[0]=='a'
  actual_mids.append([v[0]%p for v in j[1]] if j is not None else None)
 assert actual_mids==row['midpoints']
 can=False
 for i0,(P,Q) in enumerate(((n,m),(m,n))):
  a=P//gcd(P,2); b=Q//2 if actual_mids[1-i0]==[0,0] else Q
  compatible=gcd(a,b)==1 and n0_H%gcd(a,L0)==0 and (n0_H-1)%gcd(b,L0)==0
  assert compatible==row['orientations'][i0]['necessary_order_CRT']
  can|=compatible and b==29
 if can:left.append(p)
assert left==[415721,6469193,9807649]
print('weak anchor-compatible opposite quotient order29',left)
# Directed decimal arithmetic unlike the producer's fixed binary Ball.
lo=Context(prec=4800,rounding=ROUND_FLOOR)
hi=Context(prec=4800,rounding=ROUND_CEILING)
class I:
 def __init__(self,a,b=None):
    self.a=Decimal(a);self.b=Decimal(a if b is None else b)
    assert self.a<=self.b
 def __add__(self,x):
    if not isinstance(x,I):x=I(x)
    return I(lo.add(self.a,x.a),hi.add(self.b,x.b))
 __radd__=__add__
 def __neg__(self):
    return I(self.b.copy_negate(),self.a.copy_negate())
 def __sub__(self,x):return self+(-x)
 def __rsub__(self,x):return (-self)+x
 def __mul__(self,x):
    if not isinstance(x,I):x=I(x)
    L=[(a,b) for a in (self.a,self.b) for b in (x.a,x.b)]
    return I(min(lo.multiply(a,b) for a,b in L),max(hi.multiply(a,b) for a,b in L))
 __rmul__=__mul__
 def __truediv__(self,x):
    if not isinstance(x,I):x=I(x)
    assert x.a>0 or x.b<0
    L=[(a,b) for a in (self.a,self.b) for b in (x.a,x.b)]
    return I(min(lo.divide(a,b) for a,b in L),max(hi.divide(a,b) for a,b in L))
# The sqrt bracket itself is exact in integer decimal coordinates.
P=10**4800
u=isqrt(2*P*P)
u0=Decimal(u);u1=Decimal(u+1);D=Decimal(P)
rt=I(lo.divide(u0,D),hi.divide(u1,D))
assert u*u<=2*P*P<(u+1)**2
def one_rt(e):
    D=(3-e)*(3-e)
    Q=(1+e,2*e)
    def nxt(P,Q,doubling):
        x,y=P; z,w=Q
        if doubling:s=(3*x*x-D)/(2*y)
        else:s=(w-y)/(z-x)
        a=s*s-x-z
        return a,s*(x-a)-y
    # Independent right-to-left binary ladder with growing secant point.
    h=hh; A=None
    while h:
        if h&1:A=Q if A is None else nxt(A,Q,False)
        h>>=1
        if h:Q=nxt(Q,Q,True)
    x,y=A
    return (2*y)/(x*x+D)
R=one_rt(rt)*one_rt(-rt)
S=Decimal(2**64)
w=T['real_norm_interval_div_2pow64']
L=hi.divide(Decimal(w[0]),S); U=lo.divide(Decimal(w[1]),S)
assert L<=R.a<=R.b<=U and (R.b<Decimal('-0.01') or R.a>Decimal('0.01'))
print('independent directed-decimal LSB enclosure in archived dyadic interval:',w)
