#!/usr/bin/env python3
"""Literal candidate theta coefficients from the same mod-13 λ; see paper.

All lattice points, local weight values and operator orientations are exact.
No p-adic newform solver or assumption that a checked row stays nonzero.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from collections import Counter
from math import isqrt
from pathlib import Path
import hashlib
import json
import sys

P=53
DETECTOR=13
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'ACTUAL-ODD2544-MARKED-ORDERS-Q29.json'
FUND_WEIGHT_TYPEI_PLUS=(17,19)
FUND_WEIGHT_TYPEI_MINUS=(5,7,13,17,19)
ROOTS_I_AT_13=(5,8)
DREF=146965*323


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def smul(k,a):
    return tuple(k*x for x in a)


def inner(a,b):
    return Q(disc_(add(a,b))-disc_(a)-disc_(b),2)


def disc_(v):
    """Positive discriminant numerator in (omega, gamma, omega gamma) x 1."""
    b,c,d=v
    C=c-2*d
    E=2*c-d
    return 3*(3*b+E)**2+4*P*(C*C-C*E+E*E)


def gs(V):
    star=[]; co=[]; n=[]
    for v in V:
        c=[inner(v,w)/d for w,d in zip(star,n)]
        co.append(c)
        w=tuple(Q(x) for x in v)
        for t,y in zip(c,star):
            w=add(w,smul(-t,y))
        star.append(w); n.append(disc_(w))
    return co,n


def reduce_basis(V):
    V=list(V)
    k=1
    while k<len(V):
        mu,N=gs(V)
        for j in reversed(range(k)):
            l=(mu[k][j]+Q(1,2)).__floor__()
            if l:
                V[k]=add(V[k],smul(-l,V[j]))
                mu,N=gs(V)
        if N[k]>=(Q(3,4)-mu[k][k-1]**2)*N[k-1]:
            k+=1
        else:
            V[k],V[k-1]=V[k-1],V[k]
            k=max(1,k-1)
    return V


def exact_reps(order,den):
    # First HNF column is literal 1, then quotient by scalars.
    assert tuple(r[0] for r in order)==(den,0,0,0)
    V=reduce_basis([tuple(order[i][j] for i in range(1,4)) for j in range(1,4)])
    a,b,c=[disc_(v) for v in V]
    p,q,r=[int(2*inner(V[i],V[j])) for i,j in ((0,1),(0,2),(1,2))]
    g=4*a*b*c+p*q*r-a*r*r-b*q*q-c*p*p
    assert g>0
    z0=9*den*den*DREF
    X=isqrt((z0*(4*b*c-r*r))//g)
    Y=isqrt((z0*(4*a*c-q*q))//g)
    for x in range(-X,X+1):
        x0=a*x*x
        for y in range(-Y,Y+1):
            z1=q*x+r*y
            delta=z1*z1+4*c*(z0-x0-b*y*y-p*x*y)
            if delta<0:
                continue
            s=isqrt(delta)
            if s*s!=delta:
                continue
            for t in ((s,-s) if s else (0,)):
                z,rem=divmod(t-z1,2*c)
                if rem:
                    continue
                w=add(add(smul(x,V[0]),smul(y,V[1])),smul(z,V[2]))
                assert disc_(w)==z0
                yield w


def leg(x,p):
    u=pow(x%p,(p-1)//2,p)
    return -1 if u==p-1 else u


@lru_cache(maxsize=None)
def zstar(p):
    return next(x for x in product(range(p),repeat=3) if any(x) and disc_(x)%p==0)


def wtI(v,den,p):
    # Delta=−disc_/9; v and zstar are in the identical O/ℤ mod p.
    y=tuple(x*pow(den,-1,p)%p for x in v)
    if not any(y) or disc_(y)%p:
        return 0
    z=zstar(p)
    # sign in (4.1): -<y,z>_Delta = (disc_(y+z)-disc_(y)-disc_(z))/9.
    b=(disc_(add(y,z))-disc_(y)-disc_(z))*pow(9,-1,p)%p
    if b:
        return leg(b,p)
    j=next(i for i,zj in enumerate(z) if zj)
    s=y[j]*pow(z[j],-1,p)%p
    assert s and y==tuple(s*zi%p for zi in z)
    return leg(s,p)


def matrix_mod_factory(mats,n):
    @lru_cache(maxsize=None)
    def ev(v,den):
        d0=pow(den,-1,n)
        return tuple(sum(t*A[i][j] for t,A in zip(v,mats[1:]))*d0%n
                     for i,j in ((0,0),(0,1),(1,0),(1,1)))
    return ev


def lines(n,l):
    return [(1,i) for i in range(n)]+[(l*i,1) for i in range(n//l)]


def marked_values(A,n,ell):
    a,b,c,d=A
    out={}
    for x,y in lines(n,ell):
        U=(a*x+b*y)%n
        V=(c*x+d*y)%n
        if (x*V-y*U)%n:
            continue
        e=U if x==1 else V
        out[x,y]=e
    assert len(out)==2
    return out


def weighted_ref(book):
    mm={int(v):matrix_mod_factory(A,int(v)) for v,A in book['exact_level_matrices'].items()}
    u=next(u for u in range(2,P) if pow(u,26,P)==P-1 and pow(u,4,P)!=1)
    log={pow(u,k,P):k for k in range(P-1)}
    assert len(log)==P-1
    output=[]
    for cls in book['marked_classes']:
        den=cls['basis_denominator']
        rows={tuple(tuple(v) for v in row['inverse_transport_mark']):row['lambda13_phi0']
              for row in cls['exact_marks']}
        a0,c0,d0=0,0,0
        stats=Counter()
        transport_plus=1 if den==1 else leg(-323,29)
        transport_minus=1 if den==1 else leg(146965,29)
        for v in exact_reps(cls['max_order_basis_columns'],den):
            stats['all_reps']+=1
            weights={l:wtI(v,den,l) for l in FUND_WEIGHT_TYPEI_MINUS}
            plus=weights[17]*weights[19]*transport_plus
            minus=weights[5]*weights[7]*weights[13]*weights[17]*weights[19]*transport_minus
            if not (plus or minus):
                continue
            stats['nonzero_typeI']+=1
            vv16=mm[16](tuple(x%16 for x in v),den)
            vv3=mm[3](tuple(x%3 for x in v),den)
            mark16=marked_values(vv16,16,2)
            mark3=marked_values(vv3,3,3)
            # At 53, reducing A+B·F leaves only A. The quotient along z=omega
            # in the type-II functional reads A's omega coefficient.
            T=(3*v[0]+2*v[1]-v[2])*pow(3*den,-1,P)%P
            assert T
            negquartic=(-log[T])%4
            for t16,t3 in product(mark16,mark3):
                key=t16,t3
                if key not in rows:
                    continue
                # Both ordinary marked eigenvalues are distinct mod3.
                val=rows[key]*leg(2*mark3[t3]-vv3[0]-vv3[-1],3)
                assert leg(2*mark3[t3]-vv3[0]-vv3[-1],3)
                stats['marked_reps']+=1
                a0+=val*plus
                if negquartic in (0,2):
                    c0+=val*minus*(1 if negquartic==0 else -1)
                else:
                    d0+=val*minus*(1 if negquartic==1 else -1)
        output.append(dict(j=cls['j'],pos_D_coeff=a0,neg_D_coeff_a_plus_i_b=[c0,d0],
                           stats=stats,actual_q29_transports=[transport_plus,transport_minus]))
    pos=sum(row['pos_D_coeff'] for row in output)
    real,imag=(sum(row['neg_D_coeff_a_plus_i_b'][i] for row in output) for i in range(2))
    return dict(discriminant=-DREF,primitive_53_root=u,class_output=output,
        pos_D_l_minus323=pos,neg_D_l_146965=[real,imag],
        mod13_pos=pos%13,mod13_neg_and_conj=[(real+j*imag)%13 for j in ROOTS_I_AT_13])


if __name__=='__main__':
    src=SOURCE.read_bytes()
    assert hashlib.sha256(src).hexdigest().startswith('aa650e28')
    print(json.dumps(weighted_ref(json.loads(src)),indent=2,sort_keys=True))
