#!/usr/bin/env python3
"""Sparse exact finite W_m-fixed label, and numeric 17-fibre normalization guards."""
import json
from itertools import product
from math import gcd, prod, isqrt

P=61
W=251895
PS=(2,3,5,7,11,37,2399)
WS=(-1,+1,+1,-1,+1,-1,+1)
N=prod(PS)

def f(x): return (x%P,0)
def add(x,y): return ((x[0]+y[0])%P,(x[1]+y[1])%P)
def neg(x): return ((-x[0])%P,(-x[1])%P)
def sub(x,y): return add(x,neg(y))
def mul(x,y): return ((x[0]*y[0]+2*x[1]*y[1])%P,(x[0]*y[1]+x[1]*y[0])%P)
def powf(x,n):
    a=f(1)
    while n:
        if n&1: a=mul(a,x)
        x=mul(x,x); n//=2
    return a
def div(x,y):
    assert y!=f(0)
    return mul(x,powf(y,P*P-2))

F2=list(product(range(P),repeat=2))
SQ={}
for z in F2: SQ.setdefault(mul(z,z),[]).append(z)
A,B=f(-35),f(-98)
def rhs(x): return add(add(powf(x,3),mul(A,x)),B)
def valid(X): return X is None or mul(X[1],X[1])==rhs(X[0])

def eadd(X,Y):
    if X is None: return Y
    if Y is None: return X
    x,y=X;u,v=Y
    if x==u and add(y,v)==f(0): return None
    m=div(sub(v,y),sub(u,x)) if x!=u else div(add(mul(f(3),mul(x,x)),A),mul(f(2),y))
    t=sub(sub(mul(m,m),x),u)
    Z=(t,sub(mul(m,sub(x,t)),y))
    assert valid(Z)
    return Z

def eneg(X): return None if X is None else (X[0],neg(X[1]))
def emul(n,Q):
    R=None
    if n<0: n,Q=-n,eneg(Q)
    while n:
        if n&1:R=eadd(R,Q)
        Q=eadd(Q,Q);n//=2
    return R

def frob(Q):return None if Q is None else tuple(powf(x,P) for x in Q)

def gamma_setup():
    roots=[t for t in F2 if rhs(t)==f(0)]
    tor=next(t for t in roots if t[1])
    a=mul(f(3),tor);b=add(mul(f(3),mul(tor,tor)),A)
    a1=mul(f(-2),a);b1=sub(mul(a,a),mul(f(4),b))
    A1=sub(b1,div(mul(a1,a1),f(3)))
    B1=sub(div(mul(f(2),powf(a1,3)),f(27)),div(mul(a1,b1),f(3)))
    s,=[s for s in F2 if s!=f(0) and mul(powf(s,4),A)==A1 and mul(powf(s,6),B)==B1
         and add(s,div(f(2),s))==f(1)]
    return roots,tor,a,b,a1,b1,A1,B1,s

def neg_poly(d,q):
    v=pow(-d%q,(q-1)//2,q)
    return -1 if v==q-1 else v

def main():
    # Counting roots only in F61, not F61². Use this exact second count, including y=0.
    n1=1+sum(1 for x in range(P) for y in range(P) if mul(f(y),f(y))==rhs(f(x)))
    n2=1+sum(len(SQ.get(rhs(x),[])) for x in F2)
    assert (n1,n2)==(62,3844)
    assert div(f(1728*4*(-35)**3),f(4*(-35)**3+27*(-98)**2))==f(41)
    roots,tor,a,b,a1,b1,A1,B1,s=gamma_setup()
    def gamma(Q):
        if Q is None or Q==(tor,f(0)):return None
        x,y=Q
        X=sub(x,tor); Yo=sub(y,mul(y,div(b,mul(X,X))))
        Xo=add(add(X,a),div(b,X))
        Z=(div(add(Xo,div(a1,f(3))),powf(s,2)),div(Yo,powf(s,3)))
        assert valid(Z)
        return Z
    def I(Q):return eadd(emul(2,gamma(Q)),eneg(Q))
    def alpha(Q):return eadd(eadd(emul(164,I(Q)),emul(14,frob(Q))),emul(11,I(frob(Q))))
    pts=[None]+[(x,y) for x in F2 for y in SQ.get(rhs(x),[])]
    # 12 rectangular samples include geometric points with nonzero imaginary coordinates
    # and the kernel/domain branches. Proof of endomorphism relations is not sampling.
    sample=pts[:6]+[q for q in pts if q and q[0][1]][:6]
    for Q in sample:
        assert I(I(Q))==emul(-7,Q) and frob(frob(Q))==emul(-61,Q)
        assert I(frob(Q))==eneg(frob(I(Q)))
        assert alpha(alpha(Q))==emul(-W,Q)
    C2=[z for z in roots if alpha((z,f(0)))==(z,f(0))]
    assert C2==[f(7)]
    assert 7*164**2+61*14**2+7*61*11**2==W
    assert powf(s,P)==sub(f(1),s)
    assert all(W%p==0 for p in (3,5,7,2399))
    keep=[]
    for mask in range(1,128):
        d=prod(p for i,p in enumerate(PS) if mask>>i&1)
        sig=prod(w for i,w in enumerate(WS) if mask>>i&1)
        if sig==-1 and neg_poly(d,61)==-1 and all(neg_poly(d,p)==1 for p in PS[1:] if d%p):
            keep.append(d)
    assert keep==[W]
    assert -W%8==1
    split={p:[e for e in range(p) if (e**2-e+(1+W)//4)%p==0] for p in (2,11,37)}
    split_a={p:[e for e in range(1,p) if (e*e+W)%p==0] for p in (11,37)}
    assert all(len(v)==2 for v in (*split.values(),*split_a.values()))
    assert (10*10)%17==15 and pow(10,8,17)==16 and pow(10,16,17)==1
    assert 17 not in PS and prod(p-1 for p in PS)%17!=0
    print(json.dumps({
      'fixed_negative_Wd_candidate':W,
      'conductor1_zero_canary_Disc':-W,
      'conductor1_forward_CM_w_roots':split,
      'same_level_finite_label':{'curve':'y^2=x^3-35x-98','j':41,'F61':n1,'F61_squared':n2,
       'f61square_basis_square':2,'velu_kernel':tor,'velu_a_b':[a,b],'quotient_C2_coeffs':[a1,b1],
       'quotient_short_coeffs':[A1,B1],'isomorphism_scale_and_tangent':s,
       'alpha_in_I_F_IF':[164,14,11],'C2_generator':[7,0],
       'ramified_kernel_factors':[3,5,7,2399],'preserved_eigenvalues_candidates':split_a,
       'tangent_s_plus_two_over_s':add(s,div(f(2),s))},
      'projected_17_torsor':{'elliptic_F61_eigenvalues':[1,10],'elliptic_F61square_eigenvalues':[1,15],
                           'order_cyclotomic_61_mod17':16,'prod_level_ell_minus1_mod17':prod(p-1 for p in PS)%17,
                           'T13_minus_eisenstein_mod17':(-2-14)%17},
    },sort_keys=True,indent=2))
if __name__=='__main__': main()
