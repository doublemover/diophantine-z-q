#!/usr/bin/env python3
"""Independent finite lifted group/CRT and real enclosure for all six incidences."""
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
T=read_pin(sys.argv[4],'d8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0')
assert len(O['rows'])==len(T['rows'])==3
assert len({x['prime'] for x in O['rows']+T['rows']})==6
assert int(O['simultaneous_h_modulus'])==int(T['prior_triad_h_modulus'])
assert int(O['simultaneous_h_residue'])==int(T['prior_triad_h_residue'])

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
assert L==int(T['old_h_preserved_modulus'])
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
assert hh%int(O['simultaneous_h_modulus'])==int(O['simultaneous_h_residue'])
assert rr%int(O['numeric_r_modulus'])==int(O['numeric_test_r'])
for j,Lrow in enumerate(O['rows']+T['rows']):
    i=j%3
    p=Lrow['prime'];m=p*p
    assert Lrow['assigned_scale']==i and p>76176 and all(p%q for q in range(2,isqrt(p)+1))
    aa,bb=Lrow['AB']; assert p==aa*aa+bb*bb
    assert (aa%16,bb%16,aa%7,bb%7,p%408)==(9,0,1,3,1)
    if j>=3:
        prior=O['rows'][i]['prime']
        assert prior==Lrow['prior_triad_prime']
        residues={l: pow(prior*p,(l-1)//2,l) for l in (5,7,11,13,19,23,41)}
        assert all(residues[l]==1 for l in (5,7,11,13,41))
        assert prior%7==p%7==3
        ell=(23,19,19)[i]
        assert residues[ell]==ell-1 and ell==Lrow['pair_still_fails_saturation_character_at']
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
    assert TT==Lrow['T_j_mod_p2'] and FF==Lrow['contact_values_mod_p2'] and TT[i]==p-1
    assert FF[i]%p==0 and FF[i]!=0 and all(FF[j]%p for j in range(3) if j!=i)
    assert all(t%p!=1 for t in (TT[i],))
    assert all(gcd(p,v)==1 for v in (2,2399,407,3,2398,439))
    assert hh%orders[0]==0 and hh%orders[1]==1 and hh%p**4==p**3
    moduli.extend([*orders,p**4])
    modulo=lcm(modulo,m)
    print(p,orders,cs,FF)
assert hh%L==h0%L and hh%5==0 and h0%5==0
assert lcm(*moduli)==int(T['simultaneous_h_modulus'])
assert int(T['simultaneous_h_residue'])==hh and T['real_passing_step']==0 and 0<hh<lcm(*moduli)
assert lcm(2*3*17,modulo)==int(T['numeric_r_modulus'])
assert 0<rr<lcm(2*3*17,modulo)

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
assert L<=R.a<=R.b<=U and R.b<Decimal('-0.01')
print('independent directed-decimal LSB enclosure in archived dyadic interval:',w)
